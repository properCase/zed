use std::{
    cell::{Cell, RefCell},
    path::{Path, PathBuf},
    rc::Rc,
    sync::Arc,
};

use anyhow::{Context as _, Result};
use askpass::EncryptedPassword;
use editor::Editor;
use futures::{FutureExt as _, channel::oneshot};
use gpui::{
    AnyWindowHandle, App, AppContext, AsyncApp, Context, Entity, PromptLevel, Subscription,
    WeakEntity, Window, WindowHandle,
};

use remote::{
    DockerConnectionOptions, Interactive, RemoteConnection, RemoteConnectionOptions,
    SshConnectionOptions, remote_connection_identity,
};
pub use settings::SshConnection;
use settings::{DevContainerConnection, ExtendingVec, RegisterSetting, Settings, WslConnection};
use util::paths::PathWithPosition;
use workspace::{
    AppState, MultiWorkspace, OpenOptions, OpenVisible, RemoteWorkspaceSource,
    SerializedWorkspaceLocation, Workspace, WorkspaceDb, WorkspaceId, WorkspaceMatching,
    find_existing_workspace, item::ItemHandle,
};

pub use remote_connection::{
    RemoteClientDelegate, RemoteConnectionModal, RemoteConnectionPrompt, SshConnectionHeader,
    connect,
};

#[derive(RegisterSetting)]
pub struct RemoteSettings {
    pub ssh_connections: ExtendingVec<SshConnection>,
    pub wsl_connections: ExtendingVec<WslConnection>,
    /// Whether to read ~/.ssh/config for ssh connection sources.
    pub read_ssh_config: bool,
}

impl RemoteSettings {
    pub fn ssh_connections(&self) -> impl Iterator<Item = SshConnection> + use<> {
        self.ssh_connections.clone().0.into_iter()
    }

    pub fn wsl_connections(&self) -> impl Iterator<Item = WslConnection> + use<> {
        self.wsl_connections.clone().0.into_iter()
    }

    pub fn fill_connection_options_from_settings(&self, options: &mut SshConnectionOptions) {
        for conn in self.ssh_connections() {
            if conn.host == options.host.to_string()
                && conn.username == options.username
                && conn.port == options.port
            {
                options.nickname = conn.nickname;
                options.upload_binary_over_ssh = conn.upload_binary_over_ssh.unwrap_or_default();
                options.args = Some(conn.args);
                options.port_forwards = conn.port_forwards;
                break;
            }
        }
    }

    pub fn connection_options_for(
        &self,
        host: String,
        port: Option<u16>,
        username: Option<String>,
    ) -> SshConnectionOptions {
        let mut options = SshConnectionOptions {
            host: host.into(),
            port,
            username,
            ..Default::default()
        };
        self.fill_connection_options_from_settings(&mut options);
        options
    }
}

#[derive(Clone, PartialEq)]
pub enum Connection {
    Ssh(SshConnection),
    Wsl(WslConnection),
    DevContainer(DevContainerConnection),
}

impl From<Connection> for RemoteConnectionOptions {
    fn from(val: Connection) -> Self {
        match val {
            Connection::Ssh(conn) => RemoteConnectionOptions::Ssh(conn.into()),
            Connection::Wsl(conn) => RemoteConnectionOptions::Wsl(conn.into()),
            Connection::DevContainer(conn) => {
                RemoteConnectionOptions::Docker(DockerConnectionOptions {
                    name: conn.name,
                    remote_user: conn.remote_user,
                    container_id: conn.container_id,
                    upload_binary_over_docker_exec: false,
                    use_podman: conn.use_podman,
                    remote_env: conn.remote_env,
                })
            }
        }
    }
}

impl From<SshConnection> for Connection {
    fn from(val: SshConnection) -> Self {
        Connection::Ssh(val)
    }
}

impl From<WslConnection> for Connection {
    fn from(val: WslConnection) -> Self {
        Connection::Wsl(val)
    }
}

impl Settings for RemoteSettings {
    fn from_settings(content: &settings::SettingsContent) -> Self {
        let remote = &content.remote;
        Self {
            ssh_connections: remote.ssh_connections.clone().unwrap_or_default().into(),
            wsl_connections: remote.wsl_connections.clone().unwrap_or_default().into(),
            read_ssh_config: remote.read_ssh_config.unwrap(),
        }
    }
}

pub struct RemoteRestoreFocus {
    focus_requested: Rc<Cell<bool>>,
    expected_window: Rc<Cell<Option<AnyWindowHandle>>>,
    _subscriptions: Rc<RefCell<Vec<Subscription>>>,
}

impl RemoteRestoreFocus {
    pub fn new(focus_requested: Rc<Cell<bool>>, cx: &mut App) -> Self {
        let expected_window = Rc::new(Cell::new(cx.active_window()));
        let subscriptions = Rc::new(RefCell::new(Vec::new()));
        let observe_window = {
            let focus_requested = focus_requested.clone();
            let expected_window = expected_window.clone();
            move |window: &mut Window, cx: &mut Context<MultiWorkspace>| {
                cx.observe_window_activation(window, {
                    let focus_requested = focus_requested.clone();
                    let expected_window = expected_window.clone();
                    move |_, window, _| {
                        let expected_active = Some(window.window_handle()) == expected_window.get();
                        if window.is_window_active() != expected_active {
                            focus_requested.set(true);
                        }
                    }
                })
            }
        };
        for window in cx.windows() {
            if let Some(window) = window.downcast::<MultiWorkspace>()
                && let Ok(subscription) =
                    window.update(cx, |_, window, cx| observe_window(window, cx))
            {
                subscriptions.borrow_mut().push(subscription);
            }
        }
        let new_workspace_subscription = cx.observe_new::<MultiWorkspace>({
            let subscriptions = Rc::downgrade(&subscriptions);
            move |_, window, cx| {
                if let Some(subscriptions) = subscriptions.upgrade()
                    && let Some(window) = window
                {
                    subscriptions.borrow_mut().push(observe_window(window, cx));
                }
            }
        });
        subscriptions.borrow_mut().push(new_workspace_subscription);
        Self {
            focus_requested,
            expected_window,
            _subscriptions: subscriptions,
        }
    }

    fn should_focus(&self, cx: &App) -> bool {
        if cx.active_window() != self.expected_window.get() {
            self.focus_requested.set(true);
        }
        !self.focus_requested.get()
    }
}

pub async fn open_remote_project(
    connection_options: RemoteConnectionOptions,
    paths: Vec<PathBuf>,
    app_state: Arc<AppState>,
    open_options: workspace::OpenOptions,
    cx: &mut AsyncApp,
) -> Result<WindowHandle<MultiWorkspace>> {
    open_remote_project_impl(connection_options, paths, app_state, open_options, None, cx).await
}

pub async fn restore_remote_project(
    connection_options: RemoteConnectionOptions,
    app_state: Arc<AppState>,
    workspace_id: WorkspaceId,
    focus: bool,
    focus_guard: &RemoteRestoreFocus,
    cx: &mut AsyncApp,
) -> Result<WindowHandle<MultiWorkspace>> {
    open_remote_project_impl(
        connection_options,
        Vec::new(),
        app_state,
        OpenOptions {
            focus: Some(focus),
            workspace_matching: WorkspaceMatching::None,
            ..OpenOptions::default()
        },
        Some(RemoteOpenSource::Restore(workspace_id, focus_guard)),
        cx,
    )
    .await
}

pub(super) enum RemoteOpenSource<'a> {
    Workspace(WindowHandle<MultiWorkspace>, WeakEntity<Workspace>),
    Restore(WorkspaceId, &'a RemoteRestoreFocus),
}

pub(super) async fn open_remote_project_impl(
    connection_options: RemoteConnectionOptions,
    paths: Vec<PathBuf>,
    app_state: Arc<AppState>,
    open_options: workspace::OpenOptions,
    source: Option<RemoteOpenSource<'_>>,
    cx: &mut AsyncApp,
) -> Result<WindowHandle<MultiWorkspace>> {
    let (restoration, requesting_workspace) = match source {
        Some(RemoteOpenSource::Restore(workspace_id, focus_guard)) => {
            (Some((workspace_id, focus_guard)), None)
        }
        Some(RemoteOpenSource::Workspace(window, workspace)) => {
            let Some(workspace) = workspace.upgrade() else {
                return Ok(window);
            };
            (None, Some((window, workspace)))
        }
        None => (None, None),
    };
    let focus_guard = restoration.map(|(_, focus_guard)| focus_guard);
    let should_focus = |cx: &App| {
        focus_guard.is_none_or(|guard| guard.should_focus(cx))
            && open_options.focus != Some(false)
            && requesting_workspace
                .as_ref()
                .is_none_or(|(window, workspace)| {
                    window
                        .read(cx)
                        .is_ok_and(|multi_workspace| multi_workspace.workspace() == workspace)
                })
    };
    let (paths, restored_position) = if let Some((workspace_id, _)) = restoration {
        let (paths, position) = cx
            .update(|cx| {
                workspace::remote_workspace_restore_info(
                    connection_options.clone(),
                    workspace_id,
                    cx,
                )
            })
            .await?;
        (paths, Some(position))
    } else {
        (paths, None)
    };

    let resolved = if open_options.workspace_matching != WorkspaceMatching::None {
        resolve_remote_paths_with_positions(&connection_options, paths.clone(), cx).await
    } else {
        None
    };
    let existing = {
        let resolved_paths = resolved.as_ref().map(|paths| {
            paths
                .iter()
                .map(|path| path.path.clone())
                .collect::<Vec<_>>()
        });
        find_existing_workspace(
            resolved_paths.as_deref().unwrap_or(&paths),
            &open_options,
            &SerializedWorkspaceLocation::Remote(connection_options.clone()),
            cx,
        )
        .await
    };

    if let Some((window, workspace)) = &requesting_workspace
        && !window.read_with(cx, |multi_workspace, cx| {
            remote_workspace_is_current(multi_workspace, workspace, cx)
        })?
    {
        return Ok(*window);
    }

    if let Some((existing_window, existing_workspace)) = &existing {
        let remote_connection = cx.update(|cx| {
            existing_workspace
                .read(cx)
                .project()
                .read(cx)
                .remote_client()
                .and_then(|client| client.read(cx).remote_connection())
        });

        if let Some(remote_connection) = remote_connection {
            let paths_with_positions = if let Some(resolved) = resolved {
                resolved
            } else {
                determine_paths_with_positions(&remote_connection, paths).await
            };

            if !existing_window.read_with(cx, |multi_workspace, cx| {
                remote_workspace_is_current(multi_workspace, existing_workspace, cx)
            })? {
                return Ok(*existing_window);
            }
            let focus = cx.update(|cx| should_focus(cx));
            existing_window.update(cx, |multi_workspace, window, cx| {
                if focus {
                    window.activate_window();
                    multi_workspace.activate(existing_workspace.clone(), None, window, cx);
                }
            })?;
            let items = open_remote_paths(
                *existing_window,
                existing_workspace,
                &paths_with_positions,
                cx,
            )
            .await?;
            navigate_to_positions(existing_window, items, &paths_with_positions, cx);

            return Ok(*existing_window);
        }
        // If the remote connection is dead (e.g. server not running after failed reconnect),
        // fall through to establish a fresh connection instead of showing an error.
        log::info!(
            "existing remote workspace found but connection is dead, starting fresh connection"
        );
    }

    let reconnect_workspace = existing.as_ref().map(|(_, workspace)| workspace.clone());
    let created_new_window = existing.is_none()
        && requesting_workspace.is_none()
        && open_options.requesting_window.is_none();
    let (window, initial_workspace) = if let Some(existing) = existing {
        existing
    } else if let Some((window, workspace)) = &requesting_workspace {
        (*window, workspace.clone())
    } else if let Some(window) = open_options.requesting_window {
        let workspace = window.update(cx, |multi_workspace, _, _| {
            multi_workspace.workspace().clone()
        })?;
        (window, workspace)
    } else {
        let workspace_position = if let Some(position) = restored_position {
            position
        } else {
            cx.update(|cx| {
                workspace::remote_workspace_position_from_db(connection_options.clone(), &paths, cx)
            })
            .await
            .context("fetching remote workspace position from db")?
        };

        let database_id = cx.update(|cx| WorkspaceDb::global(cx)).next_id().await?;
        let mut options =
            cx.update(|cx| (app_state.build_window_options)(workspace_position.display, cx));
        options.window_bounds = workspace_position.window_bounds;
        options.show = true;
        options.focus = cx.update(|cx| should_focus(cx));
        let focus = options.focus;

        let window = cx.open_window(options, |window, cx| {
            if focus
                && let Some(guard) = focus_guard
                && cx.active_window() == Some(window.window_handle())
            {
                guard.expected_window.set(Some(window.window_handle()));
            }
            let project = project::Project::local(
                app_state.client.clone(),
                app_state.node_runtime.clone(),
                app_state.user_store.clone(),
                app_state.languages.clone(),
                app_state.fs.clone(),
                None,
                project::LocalProjectFlags::default(),
                cx,
            );
            let workspace = cx.new(|cx| {
                let mut workspace =
                    Workspace::new(Some(database_id), project, app_state.clone(), window, cx);
                workspace.mark_as_remote_connection_placeholder();
                workspace.centered_layout = workspace_position.centered_layout;
                workspace
            });
            cx.new(|cx| {
                let mut multi_workspace = MultiWorkspace::new(workspace, window, cx);
                if let Some((workspace_id, _)) = restoration {
                    multi_workspace.set_restoring_workspace_id(workspace_id, cx);
                }
                multi_workspace
            })
        })?;

        let workspace = window.update(cx, |multi_workspace, _, _cx| {
            multi_workspace.workspace().clone()
        })?;
        (window, workspace)
    };

    let cancelled = loop {
        if !window.read_with(cx, |multi_workspace, cx| {
            remote_workspace_is_current(multi_workspace, &initial_workspace, cx)
        })? {
            return Ok(window);
        }
        let (cancel_tx, mut cancel_rx) = oneshot::channel();
        let focus = cx.update(|cx| should_focus(cx));
        let activate_source = requesting_workspace.is_none();
        let delegate = window.update(cx, {
            let paths = paths.clone();
            let connection_options = connection_options.clone();
            let initial_workspace = initial_workspace.clone();
            move |multi_workspace: &mut MultiWorkspace, window, cx| {
                if focus {
                    if let Some(guard) = focus_guard {
                        guard.expected_window.set(Some(window.window_handle()));
                    }
                    window.activate_window();
                }
                if activate_source && multi_workspace.workspace() != &initial_workspace {
                    multi_workspace.retain_active_workspace(cx);
                    multi_workspace.activate(initial_workspace.clone(), None, window, cx);
                }
                let inactive = multi_workspace.workspace() != &initial_workspace;
                let focused = window.focused(cx);
                let delegate = initial_workspace.update(cx, |workspace, cx| {
                    workspace.hide_modal(window, cx);
                    workspace.toggle_modal(window, cx, |window, cx| {
                        RemoteConnectionModal::new(&connection_options, paths, window, cx)
                    });

                    let ui = workspace
                        .active_modal::<RemoteConnectionModal>(cx)?
                        .read(cx)
                        .prompt
                        .clone();

                    ui.update(cx, |ui, _cx| {
                        ui.set_cancellation_tx(cancel_tx);
                    });

                    Some(Arc::new(RemoteClientDelegate::new(
                        window.window_handle(),
                        ui.downgrade(),
                        if let RemoteConnectionOptions::Ssh(options) = &connection_options {
                            options
                                .password
                                .as_deref()
                                .and_then(|pw| EncryptedPassword::try_from(pw).ok())
                        } else {
                            None
                        },
                    )))
                });
                if inactive {
                    window.defer(cx, move |window, cx| {
                        if let Some(focused) = focused {
                            window.focus(&focused, cx);
                        } else {
                            window.blur(cx);
                        }
                    });
                }
                delegate
            }
        })?;

        let Some(delegate) = delegate else { break true };

        let opened = {
            let attempt = async {
                let remote_connection =
                    remote::connect(connection_options.clone(), delegate.clone(), cx).await?;
                let paths_with_positions = if restoration.is_some() {
                    paths
                        .iter()
                        .cloned()
                        .map(PathWithPosition::from_path)
                        .collect()
                } else {
                    determine_paths_with_positions(&remote_connection, paths.clone()).await
                };
                anyhow::ensure!(
                    window.read_with(cx, |multi_workspace, cx| {
                        remote_workspace_is_current(multi_workspace, &initial_workspace, cx)
                    })?,
                    "Remote open source workspace was closed",
                );
                let (workspace, items) = cx
                    .update(|cx| {
                        workspace::open_remote_project_with_new_connection(
                            window,
                            initial_workspace.clone(),
                            remote_connection,
                            delegate.clone(),
                            app_state.clone(),
                            paths_with_positions
                                .iter()
                                .map(|path| path.path.clone())
                                .collect(),
                            reconnect_workspace
                                .as_ref()
                                .map(|workspace| {
                                    RemoteWorkspaceSource::Reconnect(workspace.clone())
                                })
                                .or_else(|| {
                                    restoration.map(|(workspace_id, _)| {
                                        RemoteWorkspaceSource::Saved(workspace_id)
                                    })
                                }),
                            cx,
                        )
                    })
                    .await?;
                let items = if reconnect_workspace.is_some()
                    && let Some(workspace) = &workspace
                {
                    open_remote_paths(window, workspace, &paths_with_positions, cx).await?
                } else {
                    items
                };
                anyhow::Ok((workspace, items, paths_with_positions))
            }
            .fuse();
            futures::pin_mut!(attempt);
            futures::select_biased! {
                _ = cancel_rx => Ok((None, Vec::new(), Vec::new())),
                result = attempt => result,
            }
        };

        initial_workspace.update(cx, |workspace, cx| {
            if let Some(ui) = workspace.active_modal::<RemoteConnectionModal>(cx) {
                ui.update(cx, |modal, cx| modal.finished(cx))
            }
        });

        match opened {
            Err(e) => {
                if !window.read_with(cx, |multi_workspace, cx| {
                    remote_workspace_is_current(multi_workspace, &initial_workspace, cx)
                })? {
                    return Ok(window);
                }
                log::error!("Failed to open project: {e:#}");
                let response = window
                    .update(cx, |_, window, cx| {
                        window.prompt(
                            PromptLevel::Critical,
                            match connection_options {
                                RemoteConnectionOptions::Ssh(_) => "Failed to connect over SSH",
                                RemoteConnectionOptions::Wsl(_) => "Failed to connect to WSL",
                                RemoteConnectionOptions::Docker(_) => {
                                    "Failed to connect to Dev Container"
                                }
                                #[cfg(any(test, feature = "test-support"))]
                                RemoteConnectionOptions::Mock(_) => {
                                    "Failed to connect to mock server"
                                }
                            },
                            Some(&format!("{e:#}")),
                            &["Retry", "Cancel"],
                            cx,
                        )
                    })?
                    .await;
                if response == Ok(0) {
                    continue;
                }

                break true;
            }

            Ok((workspace, items, paths_with_positions)) => {
                navigate_to_positions(&window, items, &paths_with_positions, cx);
                break workspace.is_none();
            }
        }
    };

    if created_new_window
        && window.read_with(cx, |multi_workspace, cx| {
            remote_workspace_is_current(multi_workspace, &initial_workspace, cx)
        })?
    {
        initial_workspace.update(cx, |workspace, _| {
            workspace.finish_remote_connection_placeholder();
        });
        if cancelled {
            if restoration.is_none()
                && let Some(panels) =
                    initial_workspace.update(cx, |workspace, _| workspace.take_panels_task())
            {
                panels
                    .await
                    .context("Failed to initialize workspace panels")?;
            }
            let serialization = window.update(cx, |multi_workspace, window, cx| {
                if !remote_workspace_is_current(multi_workspace, &initial_workspace, cx) {
                    return None;
                }
                if restoration.is_none()
                    && multi_workspace.workspaces().count() == 1
                    && multi_workspace.project_group_keys().is_empty()
                    && initial_workspace.read(cx).is_empty(cx)
                {
                    multi_workspace.close_window(&workspace::CloseWindow, window, cx);
                    None
                } else {
                    Some(initial_workspace.update(cx, |workspace, cx| {
                        workspace.flush_serialization(window, cx)
                    }))
                }
            })?;
            if let Some(serialization) = serialization {
                serialization.await;
            }
        } else {
            window
                .update(cx, |multi_workspace, window, cx| {
                    multi_workspace.remove(
                        [initial_workspace],
                        workspace::RemovalIntent::CloseProject,
                        window,
                        cx,
                    )
                })?
                .await?;
        }
    }

    Ok(window)
}

pub fn navigate_to_positions(
    window: &WindowHandle<MultiWorkspace>,
    items: impl IntoIterator<Item = Option<Box<dyn workspace::item::ItemHandle>>>,
    positions: &[PathWithPosition],
    cx: &mut AsyncApp,
) {
    for (item, path) in items.into_iter().zip(positions) {
        let Some(item) = item else {
            continue;
        };
        let Some(row) = path.row else {
            continue;
        };
        if let Some(active_editor) = item.downcast::<Editor>() {
            window
                .update(cx, |_, window, cx| {
                    active_editor.update(cx, |editor, cx| {
                        let row = row.saturating_sub(1);
                        let col = path.column.unwrap_or(0).saturating_sub(1);
                        let Some(buffer) = editor.buffer().read(cx).as_singleton() else {
                            return;
                        };
                        let buffer_snapshot = buffer.read(cx).snapshot();
                        let point = buffer_snapshot.point_from_external_input(row, col);
                        editor.go_to_singleton_buffer_point(point, window, cx);
                    });
                })
                .ok();
        }
    }
}

pub async fn resolve_remote_paths_with_positions(
    connection_options: &RemoteConnectionOptions,
    paths: Vec<PathBuf>,
    cx: &mut AsyncApp,
) -> Option<Vec<PathWithPosition>> {
    let mut candidates = paths
        .iter()
        .filter_map(|path| path.to_str())
        .map(PathWithPosition::parse_str)
        .filter(|parsed| parsed.row.is_some())
        .map(|parsed| parsed.path)
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        return Some(paths.into_iter().map(PathWithPosition::from_path).collect());
    }
    candidates.extend(paths.iter().cloned());
    let (_, workspace) = find_existing_workspace(
        &candidates,
        &OpenOptions::default(),
        &SerializedWorkspaceLocation::Remote(connection_options.clone()),
        cx,
    )
    .await?;
    let project = workspace.read_with(cx, |workspace, cx| {
        let project = workspace.project();
        let client = project.read(cx).remote_client()?;
        let client = client.read(cx);
        (client.remote_connection().is_some()
            && remote_connection_identity(&client.connection_options())
                == remote_connection_identity(connection_options))
        .then(|| project.clone())
    })?;
    Some(
        resolve_paths_with_positions(paths, async |path: &Path| {
            project
                .read_with(cx, |project, cx| {
                    project.resolve_abs_path(&path.to_string_lossy(), cx)
                })
                .await
                .is_some()
        })
        .await,
    )
}

pub(crate) async fn determine_paths_with_positions(
    remote_connection: &Arc<dyn RemoteConnection>,
    paths: Vec<PathBuf>,
) -> Vec<PathWithPosition> {
    resolve_paths_with_positions(paths, async |path: &Path| {
        path_exists(remote_connection, path).await
    })
    .await
}

async fn resolve_paths_with_positions(
    paths: Vec<PathBuf>,
    path_exists: impl AsyncFn(&Path) -> bool,
) -> Vec<PathWithPosition> {
    let mut paths_with_positions = Vec::new();
    for path in paths {
        if let Some(path_str) = path.to_str() {
            let path_with_position = PathWithPosition::parse_str(path_str);
            if path_with_position.row.is_some() && !path_exists(&path).await {
                paths_with_positions.push(path_with_position);
                continue;
            }
        }
        paths_with_positions.push(PathWithPosition::from_path(path))
    }
    paths_with_positions
}

fn remote_workspace_is_current(
    multi_workspace: &MultiWorkspace,
    workspace: &Entity<Workspace>,
    cx: &App,
) -> bool {
    multi_workspace
        .workspaces()
        .any(|current| current == workspace)
        && workspace.read(cx).session_id().as_deref()
            == Some(workspace.read(cx).app_state().session.read(cx).id())
}

async fn open_remote_paths(
    window: WindowHandle<MultiWorkspace>,
    workspace: &Entity<Workspace>,
    paths: &[PathWithPosition],
    cx: &mut AsyncApp,
) -> Result<Vec<Option<Box<dyn ItemHandle>>>> {
    let results = window
        .update(cx, |multi_workspace, window, cx| {
            anyhow::ensure!(
                remote_workspace_is_current(multi_workspace, workspace, cx),
                "Remote open target workspace was closed",
            );
            let focus = multi_workspace.workspace() == workspace;
            anyhow::Ok(workspace.update(cx, |workspace, cx| {
                workspace.open_paths(
                    paths.iter().map(|path| path.path.clone()).collect(),
                    OpenOptions {
                        visible: Some(OpenVisible::All),
                        focus: Some(focus),
                        ..OpenOptions::default()
                    },
                    None,
                    window,
                    cx,
                )
            }))
        })??
        .await;
    Ok(workspace.update(cx, |workspace, cx| {
        results
            .into_iter()
            .map(|result| {
                result.and_then(|result| match result {
                    Ok(item) => Some(item),
                    Err(error) => {
                        workspace.show_error(format!("{error}"), cx);
                        None
                    }
                })
            })
            .collect()
    }))
}

async fn path_exists(connection: &Arc<dyn RemoteConnection>, path: &Path) -> bool {
    let Ok(command) = connection.build_command(
        Some("test".to_string()),
        &["-e".to_owned(), path.to_string_lossy().to_string()],
        &Default::default(),
        None,
        None,
        Interactive::No,
    ) else {
        return false;
    };
    let Ok(mut child) = util::command::new_command(command.program)
        .args(command.args)
        .envs(command.env)
        .spawn()
    else {
        return false;
    };
    child.status().await.is_ok_and(|status| status.success())
}

#[cfg(test)]
mod tests {
    use super::*;
    use extension::ExtensionHostProxy;
    use fs::{FakeFs, Fs as _, RemoveOptions};
    use gpui::{AppContext, Focusable as _, TestAppContext, UpdateGlobal as _};
    use http_client::BlockedHttpClient;
    use node_runtime::NodeRuntime;
    use project::Project;
    use remote::RemoteClient;
    use remote_server::{HeadlessAppState, HeadlessProject};
    use rpc::proto;
    use serde_json::json;
    use settings::SettingsStore;
    use util::path;
    use workspace::{
        find_existing_workspace,
        item::{Item as _, SaveOptions},
    };

    #[gpui::test]
    async fn test_restore_remote_projects_with_overlapping_roots(cx: &mut TestAppContext) {
        for (missing_parent, reverse_roots, missing_shared) in [
            (false, false, false),
            (true, false, false),
            (true, true, false),
            (true, false, true),
        ] {
            let cx = &mut cx.new_app();
            cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
            let app_state = init_test(cx);
            cx.update(|cx| release_channel::init(semver::Version::new(0, 0, 0), cx));
            let options = RemoteConnectionOptions::Mock(remote::MockConnectionOptions { id: 0 });
            let remote_fs = FakeFs::new(cx.executor());
            let tree = json!({
                "shared": {"a.txt": "tab A"},
                "gone": {"other": {"b.txt": "tab B"}}
            });
            remote_fs.insert_tree(path!("/"), tree.clone()).await;
            let previous_client = Rc::new(RefCell::new(None::<Entity<RemoteClient>>));
            let _subscription = cx.update(|cx| {
                cx.observe_new::<MultiWorkspace>({
                    let previous_client = previous_client.clone();
                    move |_, _, cx| {
                        if let Some(client) = previous_client.borrow_mut().take() {
                            client.update(cx, |client, cx| client.force_server_not_running(cx));
                        }
                    }
                })
            });
            let focus_guard =
                Rc::new(cx.update(|cx| RemoteRestoreFocus::new(Rc::new(Cell::new(false)), cx)));
            let database = cx.update(|cx| WorkspaceDb::global(cx));
            let records = || {
                database
                    .select::<(WorkspaceId, String, String, Option<String>)>(
                        "SELECT workspace_id, paths, paths_order, contents
                         FROM workspaces LEFT JOIN editors USING (workspace_id)
                         WHERE remote_connection_id IS NOT NULL
                         ORDER BY workspace_id, contents",
                    )
                    .unwrap()()
                .unwrap()
            };
            let mut projects = [
                (
                    vec![path!("/shared")],
                    path!("/shared/a.txt"),
                    "tab A",
                    "scratch A",
                ),
                (
                    vec![path!("/shared"), path!("/gone/other")],
                    path!("/gone/other/b.txt"),
                    "tab B",
                    "scratch B",
                ),
            ];
            if reverse_roots {
                projects[1].0.reverse();
            }
            let mut saved_ids = Vec::new();
            let mut servers = Vec::new();
            for restoring in [false, true] {
                for (index, (paths, tab_path, text, scratch)) in projects.iter().enumerate() {
                    let paths = paths.iter().map(PathBuf::from).collect::<Vec<_>>();
                    let fail_restore = restoring && index == 1 && missing_parent;
                    let saved_records = fail_restore.then(&records);
                    if fail_restore {
                        for path in [
                            Some(path!("/gone")),
                            missing_shared.then_some(path!("/shared")),
                        ]
                        .into_iter()
                        .flatten()
                        {
                            remote_fs
                                .remove_dir(
                                    Path::new(path),
                                    RemoveOptions {
                                        recursive: true,
                                        ..RemoveOptions::default()
                                    },
                                )
                                .await
                                .unwrap();
                        }
                    }
                    servers.push(remote_test_server(&options, remote_fs.clone(), cx));
                    let window = if restoring {
                        let restoration = cx.spawn({
                            let options = options.clone();
                            let app_state = app_state.clone();
                            let focus_guard = focus_guard.clone();
                            let workspace_id = saved_ids[index];
                            async move |mut cx| {
                                restore_remote_project(
                                    options,
                                    app_state,
                                    workspace_id,
                                    false,
                                    &focus_guard,
                                    &mut cx,
                                )
                                .await
                            }
                        });
                        if fail_restore {
                            cx.run_until_parked();
                            assert!(cx.has_pending_prompt());
                            assert!(!restoration.is_ready());
                            assert_eq!(records(), saved_records.unwrap());
                            let live_ids = cx
                                .windows()
                                .into_iter()
                                .flat_map(|window| {
                                    window
                                        .downcast::<MultiWorkspace>()
                                        .unwrap()
                                        .read_with(cx, |multi_workspace, cx| {
                                            multi_workspace
                                                .workspaces()
                                                .filter(|workspace| {
                                                    workspace
                                                        .read(cx)
                                                        .project()
                                                        .read(cx)
                                                        .is_remote()
                                                })
                                                .filter_map(|workspace| {
                                                    workspace.read(cx).database_id()
                                                })
                                                .collect::<Vec<_>>()
                                        })
                                        .unwrap()
                                })
                                .collect::<Vec<_>>();
                            assert_eq!(live_ids, vec![saved_ids[0]]);
                            cx.executor()
                                .advance_clock(std::time::Duration::from_millis(50));
                            cx.run_until_parked();
                            remote_fs.insert_tree(path!("/"), tree.clone()).await;
                            servers.push(remote_test_server(&options, remote_fs.clone(), cx));
                            cx.simulate_prompt_answer("Retry");
                        }
                        cx.run_until_parked();
                        assert!(!cx.has_pending_prompt());
                        assert!(restoration.is_ready());
                        restoration.await
                    } else {
                        open_remote_project(
                            options.clone(),
                            paths.clone(),
                            app_state.clone(),
                            OpenOptions {
                                workspace_matching: WorkspaceMatching::None,
                                ..OpenOptions::default()
                            },
                            &mut cx.to_async(),
                        )
                        .await
                    }
                    .unwrap();

                    if !restoring {
                        let items = window
                            .update(cx, |multi_workspace, window, cx| {
                                multi_workspace.workspace().update(cx, |workspace, cx| {
                                    workspace.open_paths(
                                        vec![PathBuf::from(*tab_path)],
                                        OpenOptions::default(),
                                        None,
                                        window,
                                        cx,
                                    )
                                })
                            })
                            .unwrap()
                            .await;
                        for item in items {
                            item.unwrap().unwrap();
                        }
                        let editor = window
                            .update(cx, |multi_workspace, window, cx| {
                                multi_workspace.workspace().update(cx, |workspace, cx| {
                                    Editor::new_in_workspace(workspace, window, cx)
                                })
                            })
                            .unwrap()
                            .await
                            .unwrap();
                        window
                            .update(cx, |_, window, cx| {
                                editor.update(cx, |editor, cx| editor.insert(scratch, window, cx));
                            })
                            .unwrap();
                    }
                    let (workspace_id, serialization) = window
                        .update(cx, |multi_workspace, window, cx| {
                            multi_workspace.workspace().update(cx, |workspace, cx| {
                                let project = workspace.project().read(cx);
                                assert!(project.is_remote());
                                *previous_client.borrow_mut() = project.remote_client();
                                assert_eq!(
                                    workspace
                                        .items_of_type::<Editor>(cx)
                                        .map(|editor| editor.read(cx).text(cx))
                                        .collect::<Vec<_>>(),
                                    vec![text.to_string(), scratch.to_string()]
                                );
                                assert_eq!(
                                    workspace.root_paths(cx),
                                    paths
                                        .iter()
                                        .map(|path| Arc::<Path>::from(Path::new(path)))
                                        .collect::<Vec<_>>(),
                                    "missing_parent={missing_parent}, reverse_roots={reverse_roots}, missing_shared={missing_shared}, restoring={restoring}, index={index}"
                                );
                                (
                                    workspace.database_id().unwrap(),
                                    workspace.flush_serialization(window, cx),
                                )
                            })
                        })
                        .unwrap();
                    serialization.await;
                    if restoring {
                        assert_eq!(workspace_id, saved_ids[index]);
                    } else {
                        saved_ids.push(workspace_id);
                        window
                            .update(cx, |_, window, _| window.remove_window())
                            .unwrap();
                        cx.run_until_parked();
                    }
                }
                let expected = saved_ids
                    .iter()
                    .zip(&projects)
                    .flat_map(|(&workspace_id, (paths, _, _, scratch))| {
                        let mut sorted_paths = paths.clone();
                        sorted_paths.sort_unstable();
                        let order = sorted_paths
                            .iter()
                            .map(|path| {
                                paths
                                    .iter()
                                    .position(|candidate| candidate == path)
                                    .unwrap()
                                    .to_string()
                            })
                            .collect::<Vec<_>>()
                            .join(",");
                        let paths = sorted_paths.join("\n");
                        [
                            (workspace_id, paths.clone(), order.clone(), None),
                            (workspace_id, paths, order, Some(scratch.to_string())),
                        ]
                    })
                    .collect::<Vec<_>>();
                assert_eq!(records(), expected);
                if !restoring && !missing_parent {
                    for (connection_options, workspace_id) in [
                        (options.clone(), WorkspaceId::from_i64(i64::MAX)),
                        (
                            RemoteConnectionOptions::Mock(remote::MockConnectionOptions { id: 1 }),
                            saved_ids[0],
                        ),
                    ] {
                        let restoration = cx.spawn({
                            let app_state = app_state.clone();
                            let focus_guard = focus_guard.clone();
                            async move |mut cx| {
                                restore_remote_project(
                                    connection_options,
                                    app_state,
                                    workspace_id,
                                    false,
                                    &focus_guard,
                                    &mut cx,
                                )
                                .await
                            }
                        });
                        cx.run_until_parked();
                        assert!(restoration.is_ready());
                        assert!(restoration.await.is_err());
                        assert_eq!(cx.windows().len(), 0);
                        assert_eq!(records(), expected);
                    }
                }
            }
            assert_eq!(cx.windows().len(), 2);
            assert_ne!(saved_ids[0], saved_ids[1]);
        }
    }

    #[gpui::test]
    async fn test_open_remote_project_preserves_positions_after_failed_root(
        cx: &mut TestAppContext,
    ) {
        for missing_first in [true, false] {
            let cx = &mut cx.new_app();
            let app_state = init_test(cx);
            cx.update(|cx| release_channel::init(semver::Version::new(0, 0, 0), cx));
            let options = RemoteConnectionOptions::Mock(remote::MockConnectionOptions { id: 0 });
            let remote_fs = FakeFs::new(cx.executor());
            remote_fs
                .insert_tree(path!("/project"), json!({"file.txt": "first\nsecond"}))
                .await;
            let _server = remote_test_server(&options, remote_fs, cx);
            let mut paths = vec![
                PathBuf::from(path!("/missing/parent/file.txt:1:1")),
                PathBuf::from(path!("/project/file.txt:2:1")),
            ];
            if !missing_first {
                paths.reverse();
            }
            let window = open_remote_project(
                options,
                paths,
                app_state,
                OpenOptions::default(),
                &mut cx.to_async(),
            )
            .await
            .unwrap();
            window
                .update(cx, |multi_workspace, _, cx| {
                    let editors = multi_workspace
                        .workspace()
                        .read(cx)
                        .items_of_type::<Editor>(cx)
                        .collect::<Vec<_>>();
                    assert_eq!(editors.len(), 1);
                    editors[0].update(cx, |editor, cx| {
                        let snapshot = editor.display_snapshot(cx);
                        assert_eq!(editor.text(cx), "first\nsecond");
                        assert_eq!(
                            editor
                                .selections
                                .newest::<language::Point>(&snapshot)
                                .head(),
                            language::Point::new(1, 0)
                        );
                    });
                })
                .unwrap();
        }
    }

    #[gpui::test]
    async fn test_find_existing_workspace_does_not_reuse_workspace_from_another_remote(
        cx: &mut TestAppContext,
        server_cx: &mut TestAppContext,
    ) {
        let app_state = init_test(cx);
        let executor = cx.executor();

        cx.update(|cx| {
            release_channel::init(semver::Version::new(0, 0, 0), cx);
        });
        server_cx.update(|cx| {
            release_channel::init(semver::Version::new(0, 0, 0), cx);
        });

        let (opts, server_session, connect_guard) = RemoteClient::fake_server(cx, server_cx);

        let remote_fs = FakeFs::new(server_cx.executor());
        remote_fs
            .insert_tree(
                path!("/project"),
                json!({
                    "src": {
                        "main.rs": "fn main() {}",
                        "lib.rs": "pub fn hello() {}",
                    },
                    "README.md": "# Test Project",
                }),
            )
            .await;

        server_cx.update(HeadlessProject::init);
        let http_client = Arc::new(BlockedHttpClient);
        let node_runtime = NodeRuntime::unavailable();
        let languages = Arc::new(language::LanguageRegistry::new(server_cx.executor()));
        let proxy = Arc::new(ExtensionHostProxy::new());

        let _headless = server_cx.new(|cx| {
            HeadlessProject::new(
                HeadlessAppState {
                    session: server_session,
                    fs: remote_fs.clone(),
                    http_client,
                    node_runtime,
                    languages,
                    extension_host_proxy: proxy,
                    startup_time: std::time::Instant::now(),
                },
                false,
                cx,
            )
        });

        drop(connect_guard);

        // First open: create a new window for the remote project.
        let paths = vec![PathBuf::from(path!("/project"))];
        let mut async_cx = cx.to_async();
        open_remote_project(
            opts.clone(),
            paths,
            app_state.clone(),
            workspace::OpenOptions::default(),
            &mut async_cx,
        )
        .await
        .expect("first open_remote_project should succeed");

        executor.run_until_parked();

        assert_eq!(
            cx.update(|cx| cx.windows().len()),
            1,
            "First open should create exactly one window"
        );

        let first_window = cx.update(|cx| cx.windows()[0].downcast::<MultiWorkspace>().unwrap());
        let first_workspace = first_window
            .read_with(cx, |multi_workspace, _| multi_workspace.workspace().clone())
            .unwrap();

        let (other_opts, other_server_session, other_connect_guard) =
            RemoteClient::fake_server(cx, server_cx);
        let ping_handler = server_cx.new(|_| ());
        other_server_session.add_request_handler::<proto::Ping, _, _, _>(
            ping_handler.downgrade(),
            |_, _, _| async { Ok(proto::Ack {}) },
        );
        drop(other_connect_guard);
        let other_remote_client = RemoteClient::connect_mock(other_opts.clone(), cx).await;
        let other_project = cx.update(|cx| {
            Project::remote(
                other_remote_client,
                app_state.client.clone(),
                app_state.node_runtime.clone(),
                app_state.user_store.clone(),
                app_state.languages.clone(),
                app_state.fs.clone(),
                false,
                cx,
            )
        });
        first_window
            .update(cx, |multi_workspace, window, cx| {
                let other_workspace =
                    cx.new(|cx| Workspace::new(None, other_project, app_state.clone(), window, cx));
                multi_workspace.add(other_workspace, window, cx);
            })
            .unwrap();

        let search_paths = vec![PathBuf::from(path!("/project/src/lib.rs"))];
        let found = find_existing_workspace(
            &search_paths,
            &workspace::OpenOptions::default(),
            &SerializedWorkspaceLocation::Remote(other_opts),
            &mut async_cx,
        )
        .await;
        assert!(
            found.is_none(),
            "a matching path on another remote must not satisfy the request"
        );

        // Verify find_existing_workspace discovers the remote workspace.
        let found = find_existing_workspace(
            &search_paths,
            &workspace::OpenOptions::default(),
            &SerializedWorkspaceLocation::Remote(opts.clone()),
            &mut async_cx,
        )
        .await;

        assert!(
            found.is_some(),
            "find_existing_workspace should locate the existing remote workspace"
        );
        let (found_window, found_workspace) = found.unwrap();
        assert_eq!(
            found_window, first_window,
            "find_existing_workspace should return the same window"
        );
        assert_eq!(
            found_workspace, first_workspace,
            "find_existing_workspace should return the workspace for the requested remote"
        );

        // Second open with the same connection options should reuse the window.
        let second_paths = vec![PathBuf::from(path!("/project/src/lib.rs"))];
        open_remote_project(
            opts.clone(),
            second_paths,
            app_state.clone(),
            workspace::OpenOptions::default(),
            &mut async_cx,
        )
        .await
        .expect("second open_remote_project should succeed via reuse");

        executor.run_until_parked();

        assert_eq!(
            cx.update(|cx| cx.windows().len()),
            1,
            "Second open should reuse the existing window, not create a new one"
        );

        let still_first_window =
            cx.update(|cx| cx.windows()[0].downcast::<MultiWorkspace>().unwrap());
        assert_eq!(
            still_first_window, first_window,
            "The window handle should be the same after reuse"
        );
    }

    #[gpui::test]
    async fn test_reopen_existing_remote_root_treats_root_as_directory(
        cx: &mut TestAppContext,
        server_cx: &mut TestAppContext,
    ) {
        let app_state = init_test(cx);
        let executor = cx.executor();

        cx.update(|cx| {
            release_channel::init(semver::Version::new(0, 0, 0), cx);
        });
        server_cx.update(|cx| {
            release_channel::init(semver::Version::new(0, 0, 0), cx);
        });

        let (opts, server_session, connect_guard) = RemoteClient::fake_server(cx, server_cx);

        let remote_fs = FakeFs::new(server_cx.executor());
        let remote_home = paths::home_dir();
        let canonical_project_path = remote_home.join("remote-reopen-root-project");
        remote_fs
            .insert_tree(
                &canonical_project_path,
                json!({
                    "src": {
                        "main.rs": "fn main() {}",
                    },
                    "README.md": "# Test Project",
                }),
            )
            .await;

        server_cx.update(HeadlessProject::init);
        let http_client = Arc::new(BlockedHttpClient);
        let node_runtime = NodeRuntime::unavailable();
        let languages = Arc::new(language::LanguageRegistry::new(server_cx.executor()));
        let proxy = Arc::new(ExtensionHostProxy::new());

        let _headless = server_cx.new(|cx| {
            HeadlessProject::new(
                HeadlessAppState {
                    session: server_session,
                    fs: remote_fs.clone(),
                    http_client,
                    node_runtime,
                    languages,
                    extension_host_proxy: proxy,
                    startup_time: std::time::Instant::now(),
                },
                false,
                cx,
            )
        });

        drop(connect_guard);

        let mut async_cx = cx.to_async();
        let window = open_remote_project(
            opts,
            vec![canonical_project_path.clone()],
            app_state,
            workspace::OpenOptions::default(),
            &mut async_cx,
        )
        .await
        .expect("initial open_remote_project should succeed");

        executor.run_until_parked();

        let open_results = window
            .update(cx, |multi_workspace, window, cx| {
                let workspace = multi_workspace.workspace().clone();
                workspace.update(cx, |workspace, cx| {
                    workspace.open_paths(
                        vec![canonical_project_path.clone()],
                        workspace::OpenOptions {
                            visible: Some(workspace::OpenVisible::All),
                            ..Default::default()
                        },
                        None,
                        window,
                        cx,
                    )
                })
            })
            .unwrap()
            .await;

        assert_eq!(open_results.len(), 1, "should return one open result");
        assert!(
            open_results[0].is_none(),
            "reopening a remote root directory should not try to open it as a file"
        );
    }

    #[gpui::test]
    async fn test_reconnect_when_server_not_running(cx: &mut TestAppContext) {
        for (multiple_roots, requested_path) in [
            (false, path!("/project")),
            (false, path!("/project/file.txt")),
            (true, path!("/project")),
            (true, path!("/project/new.txt:2:2")),
        ] {
            for (restore_unsaved_buffers, multi_workspace_enabled) in
                [(true, false), (false, false), (true, true), (false, true)]
            {
                let case = format!(
                    "multiple_roots={multiple_roots}, requested_path={requested_path}, restore_unsaved_buffers={restore_unsaved_buffers}, multi_workspace_enabled={multi_workspace_enabled}"
                );
                let cx = &mut cx.new_app();
                cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
                let app_state = init_test(cx);
                cx.update(|cx| {
                    release_channel::init(semver::Version::new(0, 0, 0), cx);
                    SettingsStore::update_global(cx, |store, cx| {
                        store.update_user_settings(cx, |settings| {
                            settings
                                .session
                                .get_or_insert_default()
                                .restore_unsaved_buffers = Some(restore_unsaved_buffers);
                            settings.agent.get_or_insert_default().enabled =
                                Some(multi_workspace_enabled);
                        });
                    });
                });
                let options =
                    RemoteConnectionOptions::Mock(remote::MockConnectionOptions { id: 0 });
                let remote_fs = FakeFs::new(cx.executor());
                remote_fs
                    .insert_tree(
                        path!("/"),
                        json!({
                            "other": {},
                            "project": {
                                "file.txt": "saved",
                                "new.txt": "first\nsecond",
                            },
                        }),
                    )
                    .await;
                let _server = remote_test_server(&options, remote_fs.clone(), cx);
                let paths = if multiple_roots {
                    vec![
                        PathBuf::from(path!("/other")),
                        PathBuf::from(path!("/project")),
                    ]
                } else {
                    vec![PathBuf::from(path!("/project"))]
                };
                let window = open_remote_project(
                    options.clone(),
                    paths.clone(),
                    app_state.clone(),
                    OpenOptions::default(),
                    &mut cx.to_async(),
                )
                .await
                .unwrap();
                let source = window
                    .read_with(cx, |multi_workspace, cx| {
                        assert_eq!(
                            multi_workspace.multi_workspace_enabled(cx),
                            multi_workspace_enabled
                        );
                        multi_workspace.workspace().clone()
                    })
                    .unwrap();
                let file_editor = window
                    .update(cx, |_, window, cx| {
                        source.update(cx, |workspace, cx| {
                            workspace.open_abs_path(
                                PathBuf::from(path!("/project/file.txt")),
                                OpenOptions::default(),
                                window,
                                cx,
                            )
                        })
                    })
                    .unwrap()
                    .await
                    .unwrap()
                    .downcast::<Editor>()
                    .unwrap();
                let draft = window
                    .update(cx, |_, window, cx| {
                        source.update(cx, |workspace, cx| {
                            Editor::new_in_workspace(workspace, window, cx)
                        })
                    })
                    .unwrap()
                    .await
                    .unwrap();
                workspace::flush_windows_serialization(&[window], &mut cx.to_async()).await;
                let source_id =
                    source.read_with(cx, |workspace, _| workspace.database_id().unwrap());
                window
                    .update(cx, |_, window, cx| {
                        file_editor
                            .update(cx, |editor, cx| editor.set_text("unsaved file", window, cx));
                        draft.update(cx, |editor, cx| {
                            editor.set_text("untitled draft", window, cx)
                        });
                        source
                            .read(cx)
                            .project()
                            .read(cx)
                            .remote_client()
                            .unwrap()
                            .update(cx, |client, cx| client.force_server_not_running(cx));
                    })
                    .unwrap();
                cx.run_until_parked();
                window
                    .update(cx, |_, window, cx| {
                        let overlay = source
                            .read(cx)
                            .active_modal::<crate::disconnected_overlay::DisconnectedOverlay>(cx)
                            .unwrap();
                        window.focus(&overlay.focus_handle(cx), cx);
                        window.dispatch_action(Box::new(menu::Cancel), cx);
                    })
                    .unwrap();
                cx.run_until_parked();
                let sibling = if multi_workspace_enabled {
                    Some(
                        cx.update(|cx| {
                            Workspace::new_local(
                                Vec::new(),
                                app_state.clone(),
                                Some(window),
                                None,
                                None,
                                workspace::OpenMode::Add,
                                cx,
                            )
                        })
                        .await
                        .unwrap()
                        .workspace,
                    )
                } else {
                    None
                };
                if let Some(sibling) = &sibling {
                    window
                        .update(cx, |multi_workspace, window, cx| {
                            multi_workspace.activate(sibling.clone(), None, window, cx);
                            assert_ne!(multi_workspace.workspace(), &source);
                        })
                        .unwrap();
                }
                let _reconnected_server = remote_test_server(&options, remote_fs.clone(), cx);
                let requested_paths = if requested_path == path!("/project/new.txt:2:2") {
                    vec![
                        PathBuf::from(path!("/missing/parent/file.txt")),
                        PathBuf::from(path!("/project")),
                        PathBuf::from(requested_path),
                    ]
                } else {
                    vec![PathBuf::from(requested_path)]
                };
                let reconnected = open_remote_project(
                    options,
                    requested_paths,
                    app_state,
                    OpenOptions::default(),
                    &mut cx.to_async(),
                )
                .await
                .unwrap();
                assert_eq!(reconnected, window);
                assert_eq!(cx.windows().len(), 1);
                let (destination, file_editor) = window
                    .update(cx, |multi_workspace, _, cx| {
                        let destination = multi_workspace.workspace().clone();
                        assert_eq!(
                            destination.read(cx).notification_ids().len(),
                            usize::from(requested_path == path!("/project/new.txt:2:2")),
                            "{case}: missing-root error notification",
                        );
                        assert_eq!(
                            destination
                                .read(cx)
                                .root_paths(cx)
                                .iter()
                                .map(|path| path.to_path_buf())
                                .collect::<Vec<_>>(),
                            paths,
                            "{case}",
                        );
                        assert_ne!(destination.read(cx).database_id().unwrap(), source_id);
                        assert_eq!(
                            multi_workspace
                                .workspaces()
                                .filter(|workspace| *workspace == &source)
                                .count(),
                            0
                        );
                        if let Some(sibling) = &sibling {
                            assert_eq!(
                                multi_workspace
                                    .workspaces()
                                    .filter(|workspace| *workspace == sibling)
                                    .count(),
                                1
                            );
                        }
                        let editors = destination
                            .read(cx)
                            .items_of_type::<Editor>(cx)
                            .collect::<Vec<_>>();
                        let mut expected = vec![
                            (String::from("unsaved file"), true, true),
                            (String::from("untitled draft"), true, true),
                        ];
                        if requested_path == path!("/project/new.txt:2:2") {
                            expected.push((String::from("first\nsecond"), false, true));
                        }
                        assert_eq!(
                            editors
                                .iter()
                                .map(|editor| {
                                    let editor = editor.read(cx);
                                    (
                                        editor.text(cx),
                                        editor.is_dirty(cx),
                                        editor.capability(cx).editable(),
                                    )
                                })
                                .collect::<Vec<_>>(),
                            expected,
                            "{case}"
                        );
                        let active_editor =
                            destination.read(cx).active_item_as::<Editor>(cx).unwrap();
                        if requested_path == path!("/project/new.txt:2:2") {
                            active_editor.update(cx, |editor, cx| {
                                assert_eq!(editor.text(cx), "first\nsecond", "{case}");
                                let snapshot = editor.display_snapshot(cx);
                                assert_eq!(
                                    editor
                                        .selections
                                        .newest::<language::Point>(&snapshot)
                                        .head(),
                                    language::Point::new(1, 1),
                                    "{case}",
                                );
                            });
                        } else {
                            assert_eq!(
                                active_editor.read(cx).text(cx),
                                if requested_path == path!("/project/file.txt") {
                                    "unsaved file"
                                } else {
                                    "untitled draft"
                                },
                                "{case}",
                            );
                        }
                        (destination, editors.into_iter().next().unwrap())
                    })
                    .unwrap();
                window
                    .update(cx, |_, window, cx| {
                        let project = destination.read(cx).project().clone();
                        file_editor.update(cx, |editor, cx| {
                            editor.set_text("saved after reconnect", window, cx);
                            editor.save(
                                SaveOptions {
                                    format: false,
                                    ..SaveOptions::default()
                                },
                                project,
                                window,
                                cx,
                            )
                        })
                    })
                    .unwrap()
                    .await
                    .unwrap();
                assert_eq!(
                    remote_fs
                        .load(Path::new(path!("/project/file.txt")))
                        .await
                        .unwrap(),
                    "saved after reconnect"
                );
                cx.run_until_parked();
            }
        }
    }

    #[gpui::test]
    async fn test_remote_open_targets_inactive_workspace(cx: &mut TestAppContext) {
        for (close_source, close_during_load) in [(false, false), (true, false), (false, true)] {
            let cx = &mut cx.new_app();
            cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
            let app_state = init_test(cx);
            cx.update(|cx| release_channel::init(semver::Version::new(0, 0, 0), cx));
            app_state
                .fs
                .as_fake()
                .insert_tree(path!("/"), json!({"active": {}, "source": {}}))
                .await;
            let active = cx
                .update(|cx| {
                    Workspace::new_local(
                        vec![PathBuf::from(path!("/active"))],
                        app_state.clone(),
                        None,
                        None,
                        None,
                        workspace::OpenMode::NewWindow,
                        cx,
                    )
                })
                .await
                .unwrap();
            let source = cx
                .update(|cx| {
                    Workspace::new_local(
                        vec![PathBuf::from(path!("/source"))],
                        app_state.clone(),
                        Some(active.window),
                        None,
                        None,
                        workspace::OpenMode::Add,
                        cx,
                    )
                })
                .await
                .unwrap()
                .workspace;
            if close_source {
                active
                    .window
                    .update(cx, |multi_workspace, window, cx| {
                        multi_workspace.remove(
                            [source.clone()],
                            workspace::RemovalIntent::CloseProject,
                            window,
                            cx,
                        )
                    })
                    .unwrap()
                    .await
                    .unwrap();
            }
            let focused = active
                .workspace
                .read_with(cx, |workspace, cx| workspace.focus_handle(cx));
            active
                .window
                .update(cx, |_, window, cx| window.focus(&focused, cx))
                .unwrap();
            let options = RemoteConnectionOptions::Mock(remote::MockConnectionOptions { id: 0 });
            let remote_fs = FakeFs::new(cx.executor());
            remote_fs.insert_tree(path!("/remote"), json!({})).await;
            let _server = remote_test_server(&options, remote_fs, cx);
            if close_during_load {
                let saved_window = open_remote_project(
                    options.clone(),
                    vec![PathBuf::from(path!("/remote"))],
                    app_state.clone(),
                    OpenOptions::default(),
                    &mut cx.to_async(),
                )
                .await
                .unwrap();
                workspace::flush_windows_serialization(&[saved_window], &mut cx.to_async()).await;
                saved_window
                    .update(cx, |_, window, _| window.remove_window())
                    .unwrap();
                cx.run_until_parked();
                active
                    .window
                    .update(cx, |_, window, cx| window.focus(&focused, cx))
                    .unwrap();
            }
            let (resume, paused) = oneshot::channel();
            let paused = Rc::new(RefCell::new(Some(paused)));
            let _subscription = cx.update(|cx| {
                cx.observe_new::<Workspace>({
                    let paused = paused.clone();
                    move |workspace, _, cx| {
                        if close_during_load {
                            let paused = paused.borrow_mut().take().unwrap();
                            workspace.set_panels_task(cx.spawn(async move |_, _| {
                                paused.await?;
                                Ok(())
                            }));
                        }
                    }
                })
            });
            let opening = cx.spawn({
                let source = source.downgrade();
                async move |mut cx| {
                    open_remote_project_impl(
                        options,
                        vec![PathBuf::from(path!("/remote"))],
                        app_state,
                        OpenOptions::default(),
                        Some(RemoteOpenSource::Workspace(active.window, source)),
                        &mut cx,
                    )
                    .await
                }
            });
            if close_during_load {
                cx.run_until_parked();
                assert!(paused.borrow().is_none());
                assert!(!opening.is_ready());
                active
                    .window
                    .update(cx, |multi_workspace, window, cx| {
                        multi_workspace.remove(
                            [source.clone()],
                            workspace::RemovalIntent::CloseProject,
                            window,
                            cx,
                        )
                    })
                    .unwrap()
                    .await
                    .unwrap();
                resume.send(()).unwrap();
            }
            let window = opening.await.unwrap();
            cx.run_until_parked();
            assert_eq!(window, active.window);
            assert!(!cx.has_pending_prompt());
            window
                .update(cx, |multi_workspace, window, cx| {
                    assert_eq!(multi_workspace.workspace(), &active.workspace);
                    assert_eq!(window.focused(cx), Some(focused.clone()));
                    assert_eq!(
                        multi_workspace
                            .workspaces()
                            .filter(|workspace| workspace.read(cx).project().read(cx).is_remote())
                            .count(),
                        usize::from(!close_source && !close_during_load),
                    );
                    assert!(
                        active
                            .workspace
                            .read(cx)
                            .active_modal::<RemoteConnectionModal>(cx)
                            .is_none()
                    );
                    assert!(
                        source
                            .read(cx)
                            .active_modal::<RemoteConnectionModal>(cx)
                            .is_none()
                    );
                })
                .unwrap();
        }
    }

    #[gpui::test]
    async fn test_cancel_remote_connection_restores_local_workspace(cx: &mut TestAppContext) {
        for (
            restoring,
            after_transport,
            after_handshake,
            error_cancel,
            close_before_retry,
            quit,
            local_work,
        ) in [
            (false, false, false, false, false, false, true),
            (false, true, false, false, false, false, true),
            (false, true, true, false, false, false, true),
            (false, true, true, true, false, false, true),
            (true, false, false, false, false, false, true),
            (true, true, true, true, false, false, true),
            (false, true, true, true, true, false, true),
            (false, true, false, false, false, true, true),
            (false, false, false, false, false, false, false),
            (false, true, true, true, false, false, false),
            (true, true, true, true, false, false, false),
        ] {
            let case = format!(
                "restoring={restoring}, after_transport={after_transport}, after_handshake={after_handshake}, error_cancel={error_cancel}, close_before_retry={close_before_retry}, quit={quit}, local_work={local_work}"
            );
            let server_cx = &mut cx.new_app();
            let cx = &mut cx.new_app();
            cx.update(|cx| cx.set_global(db::AppDatabase::test_new()));
            let app_state = init_test(cx);
            cx.update(|cx| release_channel::init(semver::Version::new(0, 0, 0), cx));
            let options = RemoteConnectionOptions::Mock(remote::MockConnectionOptions { id: 0 });
            let saved_workspace_id = if restoring {
                let remote_fs = FakeFs::new(cx.executor());
                remote_fs.insert_tree(path!("/remote"), json!({})).await;
                let _server = remote_test_server(&options, remote_fs, cx);
                let saved_window = open_remote_project(
                    options.clone(),
                    vec![PathBuf::from(path!("/remote"))],
                    app_state.clone(),
                    OpenOptions::default(),
                    &mut cx.to_async(),
                )
                .await
                .unwrap();
                workspace::flush_windows_serialization(&[saved_window], &mut cx.to_async()).await;
                let (workspace_id, saved_workspace, shutdown) = saved_window
                    .update(cx, |multi_workspace, window, cx| {
                        let workspace = multi_workspace.workspace();
                        let workspace_id = workspace.read(cx).database_id().unwrap();
                        let shutdown = workspace
                            .read(cx)
                            .project()
                            .read(cx)
                            .remote_client()
                            .unwrap()
                            .update(cx, |client, cx| {
                                client.shutdown_processes(
                                    Some(proto::ShutdownRemoteServer {}),
                                    cx.background_executor().clone(),
                                )
                            })
                            .unwrap();
                        window.remove_window();
                        (workspace_id, workspace.downgrade(), shutdown)
                    })
                    .unwrap();
                shutdown.await;
                cx.run_until_parked();
                assert!(
                    saved_workspace.upgrade().is_none(),
                    "{case}: saved workspace retained after closing its window"
                );
                assert!(
                    !cx.read(|cx| remote::has_active_connection(&options, cx)),
                    "{case}: saved connection survived shutdown"
                );
                Some(workspace_id)
            } else {
                None
            };
            let database = cx.update(|cx| WorkspaceDb::global(cx));

            let (server_session, connect_guard) =
                RemoteClient::fake_server_with_opts(&options, cx, server_cx);
            let (load_sender, load_receiver) = oneshot::channel();
            let mut load_sender = Some(load_sender);
            let server = server_cx.new(|_| (false, false, Some(load_receiver)));
            server_session.add_request_handler::<proto::Ping, _, _, _>(
                server.downgrade(),
                move |server, _, mut cx| async move {
                    server.update(&mut cx, |state, _| state.0 = true);
                    if after_handshake {
                        Ok(proto::Ack {})
                    } else {
                        futures::future::pending().await
                    }
                },
            );
            server_session.add_request_handler::<proto::AddWorktree, _, _, _>(
                server.downgrade(),
                |server, _, mut cx| async move {
                    let receiver = server.update(&mut cx, |state, _| {
                        state.1 = true;
                        state.2.take().unwrap()
                    });
                    receiver.await.ok();
                    anyhow::bail!("delayed root load failed");
                },
            );
            let mut connect_guard = Some(connect_guard);
            let connection = cx.spawn({
                let app_state = app_state.clone();
                async move |mut cx| {
                    if let Some(workspace_id) = saved_workspace_id {
                        let focus_guard =
                            cx.update(|cx| RemoteRestoreFocus::new(Rc::new(Cell::new(false)), cx));
                        restore_remote_project(
                            options,
                            app_state,
                            workspace_id,
                            true,
                            &focus_guard,
                            &mut cx,
                        )
                        .await
                    } else {
                        open_remote_project(
                            options,
                            vec![PathBuf::from(path!("/remote"))],
                            app_state,
                            OpenOptions::default(),
                            &mut cx,
                        )
                        .await
                    }
                }
            });
            cx.run_until_parked();
            assert!(
                !connection.is_ready(),
                "{case}: connection completed before local setup"
            );
            assert!(
                !cx.has_pending_prompt(),
                "{case}: connection failed before local setup with transport gated"
            );
            let window = cx.windows()[0].downcast::<MultiWorkspace>().unwrap();
            let initial_workspace = window
                .read_with(cx, |multi_workspace, _| multi_workspace.workspace().clone())
                .unwrap();
            assert!(
                initial_workspace.read_with(cx, |workspace, cx| {
                    workspace
                        .active_modal::<RemoteConnectionModal>(cx)
                        .is_some()
                }),
                "{case}: connection modal missing before local setup"
            );
            if !local_work {
                initial_workspace.update(cx, |workspace, _| {
                    workspace.set_panels_task(gpui::Task::ready(Ok(())));
                });
            }
            let database_id = initial_workspace
                .read_with(cx, |workspace, _| workspace.database_id())
                .unwrap();
            assert_ne!(Some(database_id), saved_workspace_id, "{case}");
            let sibling = if local_work {
                let draft = window
                    .update(cx, |_, window, cx| {
                        initial_workspace.update(cx, |workspace, cx| {
                            Editor::new_in_workspace(workspace, window, cx)
                        })
                    })
                    .unwrap()
                    .await
                    .unwrap();
                window
                    .update(cx, |_, window, cx| {
                        if !close_before_retry {
                            draft.update(cx, |editor, cx| {
                                editor.insert("connection draft", window, cx)
                            });
                        }
                    })
                    .unwrap();
                app_state
                    .fs
                    .as_fake()
                    .insert_file(path!("/sibling.txt"), Vec::from("sibling"))
                    .await;
                Some(
                    cx.update(|cx| {
                        Workspace::new_local(
                            vec![PathBuf::from(path!("/sibling.txt"))],
                            app_state.clone(),
                            Some(window),
                            None,
                            None,
                            workspace::OpenMode::Add,
                            cx,
                        )
                    })
                    .await
                    .unwrap()
                    .workspace,
                )
            } else {
                None
            };
            assert!(
                initial_workspace.read_with(cx, |workspace, cx| {
                    workspace
                        .active_modal::<RemoteConnectionModal>(cx)
                        .is_some()
                }),
                "{case}: connection modal disappeared during local setup with transport gated"
            );
            let workspace_ids = || {
                database
                    .select::<WorkspaceId>(
                        "SELECT workspace_id FROM workspaces ORDER BY workspace_id",
                    )
                    .unwrap()()
                .unwrap()
            };
            let retained_ids = workspace_ids();
            if after_transport {
                drop(connect_guard.take());
            }
            cx.run_until_parked();
            assert_eq!(
                server.read_with(server_cx, |state, _| (state.0, state.1)),
                (after_transport, after_handshake),
                "{case}: cancellation stage not reached"
            );
            assert!(
                !connection.is_ready(),
                "{case}: connection completed before cancellation"
            );
            assert!(
                !cx.has_pending_prompt(),
                "{case}: connection failed before cancellation"
            );
            if quit {
                cx.quit();
                assert_eq!(
                    workspace_ids(),
                    retained_ids,
                    "{case}: reservation survived quit"
                );
                drop(connection);
                continue;
            }
            if error_cancel {
                load_sender.take().unwrap().send(()).unwrap();
                cx.run_until_parked();
                assert!(
                    cx.has_pending_prompt(),
                    "{case}: root-load error prompt missing"
                );
                if close_before_retry {
                    assert!(
                        window
                            .update(cx, |multi_workspace, window, cx| {
                                multi_workspace.remove(
                                    [initial_workspace.clone()],
                                    workspace::RemovalIntent::CloseProject,
                                    window,
                                    cx,
                                )
                            })
                            .unwrap()
                            .await
                            .unwrap()
                    );
                    cx.simulate_prompt_answer("Retry");
                } else {
                    cx.simulate_prompt_answer("Cancel");
                }
            } else {
                window
                    .update(cx, |_, window, cx| {
                        let modal = initial_workspace
                            .read(cx)
                            .active_modal::<RemoteConnectionModal>(cx)
                            .unwrap_or_else(|| {
                                panic!("{case}: connection modal missing at cancellation")
                            });
                        window.focus(&modal.focus_handle(cx), cx);
                        window.dispatch_action(Box::new(menu::Cancel), cx);
                    })
                    .unwrap();
            }
            cx.run_until_parked();
            assert!(
                connection.is_ready(),
                "{case}: cancellation did not complete"
            );
            assert_eq!(connection.await.unwrap(), window, "{case}");
            if let Some(load_sender) = load_sender {
                load_sender.send(()).ok();
            }
            cx.run_until_parked();
            assert!(
                !cx.has_pending_prompt(),
                "{case}: prompt remained after cancellation"
            );
            if !local_work {
                assert_eq!(cx.windows().len(), usize::from(restoring), "{case}");
                if restoring {
                    assert_eq!(workspace_ids(), retained_ids, "{case}");
                }
                continue;
            }
            assert_eq!(
                workspace_ids(),
                retained_ids,
                "{case}: reservation survived cancellation"
            );
            let sibling = sibling.unwrap();
            if close_before_retry {
                window
                    .read_with(cx, |multi_workspace, cx| {
                        assert_eq!(multi_workspace.workspace(), &sibling, "{case}");
                        assert_eq!(
                            multi_workspace.workspaces().cloned().collect::<Vec<_>>(),
                            vec![sibling.clone()],
                            "{case}",
                        );
                        assert_eq!(initial_workspace.read(cx).session_id(), None, "{case}");
                    })
                    .unwrap();
                continue;
            }
            window
                .read_with(cx, |multi_workspace, cx| {
                    assert_eq!(multi_workspace.workspace(), &initial_workspace, "{case}");
                    assert_eq!(
                        multi_workspace.workspaces().cloned().collect::<Vec<_>>(),
                        vec![initial_workspace.clone(), sibling.clone()],
                        "{case}"
                    );
                    assert_eq!(
                        initial_workspace.read(cx).database_id(),
                        Some(database_id),
                        "{case}"
                    );
                })
                .unwrap();
            assert_eq!(
                database
                    .select_row_bound::<_, String>(
                        "SELECT contents FROM editors WHERE workspace_id = ?",
                    )
                    .unwrap()(database_id)
                .unwrap(),
                Some(String::from("connection draft")),
                "{case}: cancellation did not persist the draft"
            );

            app_state
                .fs
                .as_fake()
                .insert_file(path!("/local.txt"), Vec::from("local"))
                .await;
            let opened = cx
                .update(|cx| {
                    workspace::open_paths(
                        &[PathBuf::from(path!("/local.txt"))],
                        app_state,
                        OpenOptions::default(),
                        cx,
                    )
                })
                .await
                .unwrap();
            assert_eq!(opened.window, window);
            assert_eq!(opened.workspace, initial_workspace);
        }
    }

    fn remote_test_server(
        options: &RemoteConnectionOptions,
        remote_fs: Arc<FakeFs>,
        cx: &mut TestAppContext,
    ) -> (TestAppContext, Entity<HeadlessProject>) {
        let mut server_cx = cx.new_app();
        server_cx.update(|cx| {
            release_channel::init(semver::Version::new(0, 0, 0), cx);
            HeadlessProject::init(cx);
        });
        let (session, guard) = RemoteClient::fake_server_with_opts(options, cx, &mut server_cx);
        let headless = server_cx.new(|cx| {
            HeadlessProject::new(
                HeadlessAppState {
                    session,
                    fs: remote_fs,
                    http_client: Arc::new(BlockedHttpClient),
                    node_runtime: NodeRuntime::unavailable(),
                    languages: Arc::new(language::LanguageRegistry::new(
                        cx.background_executor().clone(),
                    )),
                    extension_host_proxy: Arc::new(ExtensionHostProxy::new()),
                    startup_time: std::time::Instant::now(),
                },
                false,
                cx,
            )
        });
        drop(guard);
        (server_cx, headless)
    }

    fn init_test(cx: &mut TestAppContext) -> Arc<AppState> {
        cx.update(|cx| {
            let state = AppState::test(cx);
            crate::init(cx);
            editor::init(cx);
            state
        })
    }
}
