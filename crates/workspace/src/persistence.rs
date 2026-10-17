pub mod model;

use std::{
    borrow::Cow,
    collections::BTreeMap,
    path::{Path, PathBuf},
    str::FromStr,
    sync::Arc,
};

use chrono::{DateTime, NaiveDateTime, Utc};
use fs::Fs;

use anyhow::{Context as _, Result, bail};
use collections::{HashMap, HashSet, IndexMap, IndexSet};
use db::{
    kvp::KeyValueStore,
    query,
    sqlez::{connection::Connection, domain::Domain},
    sqlez_macros::sql,
};
use gpui::{Axis, Bounds, Task, WindowBounds, WindowId, point, size};
use project::{
    ProjectGroupKey,
    bookmark_store::SerializedBookmark,
    debugger::breakpoint_store::{BreakpointState, SourceBreakpoint},
    trusted_worktrees::{DbTrustedPaths, RemoteHostLocation},
};

use language::{LanguageName, Toolchain, ToolchainScope};
use remote::{
    DockerConnectionOptions, RemoteConnectionIdentity, RemoteConnectionOptions,
    SshConnectionOptions, WslConnectionOptions, remote_connection_identity,
};
use serde::{Deserialize, Serialize};
use sqlez::{
    bindable::{Bind, Column, StaticColumnCount},
    statement::Statement,
    thread_safe_connection::ThreadSafeConnection,
};

use ui::{App, SharedString, px};
use util::{ResultExt, maybe, rel_path::RelPath};
use uuid::Uuid;

use crate::{
    WorkspaceId,
    path_list::{PathList, SerializedPathList},
    persistence::model::RemoteConnectionKind,
};

use model::{
    GroupId, ItemId, PaneId, RemoteConnectionId, SerializedItem, SerializedPane,
    SerializedPaneGroup, SerializedWorkspace,
};

use self::model::{DockStructure, SerializedWorkspaceLocation, SessionWorkspace};

pub(crate) type WorkspaceBinding = (Option<String>, Option<u64>, Option<i64>);

#[derive(Debug)]
pub(crate) struct WorkspaceOwnershipChanged;

impl std::fmt::Display for WorkspaceOwnershipChanged {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("Saved workspace ownership changed")
    }
}

impl std::error::Error for WorkspaceOwnershipChanged {}

// https://www.sqlite.org/limits.html
// > <..> the maximum value of a host parameter number is SQLITE_MAX_VARIABLE_NUMBER,
// > which defaults to <..> 32766 for SQLite versions after 3.32.0.
const MAX_QUERY_PLACEHOLDERS: usize = 32000;

fn parse_timestamp(text: &str) -> DateTime<Utc> {
    NaiveDateTime::parse_from_str(text, "%Y-%m-%d %H:%M:%S")
        .map(|naive| naive.and_utc())
        .unwrap_or_else(|_| Utc::now())
}

fn contains_wsl_path(paths: &PathList) -> bool {
    cfg!(windows)
        && paths
            .paths()
            .iter()
            .any(|path| util::paths::WslPath::from_path(path).is_some())
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) struct SerializedAxis(pub(crate) gpui::Axis);
impl sqlez::bindable::StaticColumnCount for SerializedAxis {}
impl sqlez::bindable::Bind for SerializedAxis {
    fn bind(
        &self,
        statement: &sqlez::statement::Statement,
        start_index: i32,
    ) -> anyhow::Result<i32> {
        match self.0 {
            gpui::Axis::Horizontal => "Horizontal",
            gpui::Axis::Vertical => "Vertical",
        }
        .bind(statement, start_index)
    }
}

impl sqlez::bindable::Column for SerializedAxis {
    fn column(
        statement: &mut sqlez::statement::Statement,
        start_index: i32,
    ) -> anyhow::Result<(Self, i32)> {
        String::column(statement, start_index).and_then(|(axis_text, next_index)| {
            Ok((
                match axis_text.as_str() {
                    "Horizontal" => Self(Axis::Horizontal),
                    "Vertical" => Self(Axis::Vertical),
                    _ => anyhow::bail!("Stored serialized item kind is incorrect"),
                },
                next_index,
            ))
        })
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Default)]
pub(crate) struct SerializedWindowBounds(pub(crate) WindowBounds);

impl StaticColumnCount for SerializedWindowBounds {
    fn column_count() -> usize {
        5
    }
}

impl Bind for SerializedWindowBounds {
    fn bind(&self, statement: &Statement, start_index: i32) -> Result<i32> {
        match self.0 {
            WindowBounds::Windowed(bounds) => {
                let next_index = statement.bind(&"Windowed", start_index)?;
                statement.bind(
                    &(
                        SerializedPixels(bounds.origin.x),
                        SerializedPixels(bounds.origin.y),
                        SerializedPixels(bounds.size.width),
                        SerializedPixels(bounds.size.height),
                    ),
                    next_index,
                )
            }
            WindowBounds::Maximized(bounds) => {
                let next_index = statement.bind(&"Maximized", start_index)?;
                statement.bind(
                    &(
                        SerializedPixels(bounds.origin.x),
                        SerializedPixels(bounds.origin.y),
                        SerializedPixels(bounds.size.width),
                        SerializedPixels(bounds.size.height),
                    ),
                    next_index,
                )
            }
            WindowBounds::Fullscreen(bounds) => {
                let next_index = statement.bind(&"FullScreen", start_index)?;
                statement.bind(
                    &(
                        SerializedPixels(bounds.origin.x),
                        SerializedPixels(bounds.origin.y),
                        SerializedPixels(bounds.size.width),
                        SerializedPixels(bounds.size.height),
                    ),
                    next_index,
                )
            }
        }
    }
}

impl Column for SerializedWindowBounds {
    fn column(statement: &mut Statement, start_index: i32) -> Result<(Self, i32)> {
        let (window_state, next_index) = String::column(statement, start_index)?;
        let ((x, y, width, height), _): ((i32, i32, i32, i32), _) =
            Column::column(statement, next_index)?;
        let bounds = Bounds {
            origin: point(px(x as f32), px(y as f32)),
            size: size(px(width as f32), px(height as f32)),
        };

        let status = match window_state.as_str() {
            "Windowed" | "Fixed" => SerializedWindowBounds(WindowBounds::Windowed(bounds)),
            "Maximized" => SerializedWindowBounds(WindowBounds::Maximized(bounds)),
            "FullScreen" => SerializedWindowBounds(WindowBounds::Fullscreen(bounds)),
            _ => bail!("Window State did not have a valid string"),
        };

        Ok((status, next_index + 4))
    }
}

const DEFAULT_WINDOW_BOUNDS_KEY: &str = "default_window_bounds";

pub fn read_default_window_bounds(kvp: &KeyValueStore) -> Option<(Uuid, WindowBounds)> {
    let json_str = kvp
        .read_kvp(DEFAULT_WINDOW_BOUNDS_KEY)
        .log_err()
        .flatten()?;

    let (display_uuid, persisted) =
        serde_json::from_str::<(Uuid, WindowBoundsJson)>(&json_str).ok()?;
    Some((display_uuid, persisted.into()))
}

pub async fn write_default_window_bounds(
    kvp: &KeyValueStore,
    bounds: WindowBounds,
    display_uuid: Uuid,
) -> anyhow::Result<()> {
    let persisted = WindowBoundsJson::from(bounds);
    let json_str = serde_json::to_string(&(display_uuid, persisted))?;
    kvp.write_kvp(DEFAULT_WINDOW_BOUNDS_KEY.to_string(), json_str)
        .await?;
    Ok(())
}

#[derive(Serialize, Deserialize)]
pub enum WindowBoundsJson {
    Windowed {
        x: i32,
        y: i32,
        width: i32,
        height: i32,
    },
    Maximized {
        x: i32,
        y: i32,
        width: i32,
        height: i32,
    },
    Fullscreen {
        x: i32,
        y: i32,
        width: i32,
        height: i32,
    },
}

impl From<WindowBounds> for WindowBoundsJson {
    fn from(b: WindowBounds) -> Self {
        match b {
            WindowBounds::Windowed(bounds) => {
                let origin = bounds.origin;
                let size = bounds.size;
                WindowBoundsJson::Windowed {
                    x: f32::from(origin.x).round() as i32,
                    y: f32::from(origin.y).round() as i32,
                    width: f32::from(size.width).round() as i32,
                    height: f32::from(size.height).round() as i32,
                }
            }
            WindowBounds::Maximized(bounds) => {
                let origin = bounds.origin;
                let size = bounds.size;
                WindowBoundsJson::Maximized {
                    x: f32::from(origin.x).round() as i32,
                    y: f32::from(origin.y).round() as i32,
                    width: f32::from(size.width).round() as i32,
                    height: f32::from(size.height).round() as i32,
                }
            }
            WindowBounds::Fullscreen(bounds) => {
                let origin = bounds.origin;
                let size = bounds.size;
                WindowBoundsJson::Fullscreen {
                    x: f32::from(origin.x).round() as i32,
                    y: f32::from(origin.y).round() as i32,
                    width: f32::from(size.width).round() as i32,
                    height: f32::from(size.height).round() as i32,
                }
            }
        }
    }
}

impl From<WindowBoundsJson> for WindowBounds {
    fn from(n: WindowBoundsJson) -> Self {
        match n {
            WindowBoundsJson::Windowed {
                x,
                y,
                width,
                height,
            } => WindowBounds::Windowed(Bounds {
                origin: point(px(x as f32), px(y as f32)),
                size: size(px(width as f32), px(height as f32)),
            }),
            WindowBoundsJson::Maximized {
                x,
                y,
                width,
                height,
            } => WindowBounds::Maximized(Bounds {
                origin: point(px(x as f32), px(y as f32)),
                size: size(px(width as f32), px(height as f32)),
            }),
            WindowBoundsJson::Fullscreen {
                x,
                y,
                width,
                height,
            } => WindowBounds::Fullscreen(Bounds {
                origin: point(px(x as f32), px(y as f32)),
                size: size(px(width as f32), px(height as f32)),
            }),
        }
    }
}

fn read_multi_workspace_state(window_id: WindowId, cx: &App) -> model::MultiWorkspaceState {
    let kvp = KeyValueStore::global(cx);
    kvp.scoped("multi_workspace_state")
        .read(&window_id.as_u64().to_string())
        .log_err()
        .flatten()
        .and_then(|json| serde_json::from_str(&json).ok())
        .unwrap_or_default()
}

#[cfg(test)]
pub async fn write_multi_workspace_state(
    kvp: &KeyValueStore,
    window_id: WindowId,
    state: model::MultiWorkspaceState,
) {
    if let Ok(json_str) = serde_json::to_string(&state) {
        kvp.scoped("multi_workspace_state")
            .write(window_id.as_u64().to_string(), json_str)
            .await
            .log_err();
    }
}

pub fn read_serialized_multi_workspaces(
    session_workspaces: Vec<model::SessionWorkspace>,
    cx: &App,
) -> Vec<model::SerializedMultiWorkspace> {
    #[derive(PartialEq, Eq, Hash)]
    enum SerializedWindowId {
        Live(WindowId),
        Restoring(i64),
        Ungrouped(usize),
    }

    let db = WorkspaceDb::global(cx);
    let mut window_groups = IndexMap::default();

    for (index, session_workspace) in session_workspaces.into_iter().enumerate() {
        let restoring_window = session_workspace.window_id.and_then(|_| {
            db.restoring_window(session_workspace.workspace_id)
                .log_err()
                .flatten()
        });
        let (window_id, state) = if let Some((id, state)) = restoring_window {
            (
                Some(SerializedWindowId::Restoring(id)),
                serde_json::from_str(&state).log_err().unwrap_or_default(),
            )
        } else {
            (
                session_workspace.window_id.map(SerializedWindowId::Live),
                session_workspace
                    .window_id
                    .map(|id| read_multi_workspace_state(id, cx))
                    .unwrap_or_default(),
            )
        };
        window_groups
            .entry(window_id.unwrap_or(SerializedWindowId::Ungrouped(index)))
            .or_insert_with(|| (Vec::new(), state))
            .0
            .push(session_workspace);
    }

    window_groups
        .into_values()
        .filter_map(|(group, state)| {
            let active_workspace = state
                .active_workspace_id
                .and_then(|id| group.iter().position(|ws| ws.workspace_id == id))
                // If the persisted active workspace can't be matched (e.g. its
                // pointer was lost or its row was pruned), fall back to the
                // first workspace that actually has paths rather than blindly
                // taking index 0, so a stray scratch/empty workspace isn't
                // restored as the focused window. Only if none have paths do we
                // fall back to the first entry.
                .or_else(|| group.iter().position(|ws| !ws.paths.is_empty()))
                .or(Some(0))
                .and_then(|index| group.get(index))?
                .clone();
            let scratch_workspaces = group
                .into_iter()
                .filter(|workspace| {
                    workspace.workspace_id != active_workspace.workspace_id
                        && workspace.paths.is_empty()
                        && workspace.location == SerializedWorkspaceLocation::Local
                })
                .map(|workspace| workspace.workspace_id)
                .collect();
            Some(model::SerializedMultiWorkspace {
                active_workspace,
                scratch_workspaces,
                state,
            })
        })
        .collect()
}

const DEFAULT_DOCK_STATE_KEY: &str = "default_dock_state";

pub fn read_default_dock_state(kvp: &KeyValueStore) -> Option<DockStructure> {
    let json_str = kvp.read_kvp(DEFAULT_DOCK_STATE_KEY).log_err().flatten()?;

    serde_json::from_str::<DockStructure>(&json_str).ok()
}

pub(crate) fn prepare_default_dock_state(docks: DockStructure) -> db::Write {
    Box::new(move |connection| {
        KeyValueStore::prepare_write_kvp(
            DEFAULT_DOCK_STATE_KEY.to_owned(),
            serde_json::to_string(&docks)?,
        )(connection)
    })
}

#[derive(Debug)]
pub struct Bookmark {
    pub row: u32,
    pub label: String,
}

impl sqlez::bindable::StaticColumnCount for Bookmark {
    fn column_count() -> usize {
        // row, label
        2
    }
}

impl sqlez::bindable::Bind for Bookmark {
    fn bind(
        &self,
        statement: &sqlez::statement::Statement,
        start_index: i32,
    ) -> anyhow::Result<i32> {
        let next_index = statement.bind(&self.row, start_index)?;
        statement.bind(&self.label, next_index)
    }
}

impl Column for Bookmark {
    fn column(statement: &mut Statement, start_index: i32) -> Result<(Self, i32)> {
        let row = statement
            .column_int(start_index)
            .with_context(|| format!("Failed to read bookmark at index {start_index}"))?
            as u32;

        let (label, next_index) = String::column(statement, start_index + 1)?;

        Ok((Bookmark { row, label }, next_index))
    }
}

#[derive(Debug)]
pub struct Breakpoint {
    pub position: u32,
    pub message: Option<Arc<str>>,
    pub condition: Option<Arc<str>>,
    pub hit_condition: Option<Arc<str>>,
    pub state: BreakpointState,
}

/// Wrapper for DB type of a breakpoint
struct BreakpointStateWrapper<'a>(Cow<'a, BreakpointState>);

impl From<BreakpointState> for BreakpointStateWrapper<'static> {
    fn from(kind: BreakpointState) -> Self {
        BreakpointStateWrapper(Cow::Owned(kind))
    }
}

impl StaticColumnCount for BreakpointStateWrapper<'_> {
    fn column_count() -> usize {
        1
    }
}

impl Bind for BreakpointStateWrapper<'_> {
    fn bind(&self, statement: &Statement, start_index: i32) -> anyhow::Result<i32> {
        statement.bind(&self.0.to_int(), start_index)
    }
}

impl Column for BreakpointStateWrapper<'_> {
    fn column(statement: &mut Statement, start_index: i32) -> anyhow::Result<(Self, i32)> {
        let state = statement.column_int(start_index)?;

        match state {
            0 => Ok((BreakpointState::Enabled.into(), start_index + 1)),
            1 => Ok((BreakpointState::Disabled.into(), start_index + 1)),
            _ => anyhow::bail!("Invalid BreakpointState discriminant {state}"),
        }
    }
}

impl sqlez::bindable::StaticColumnCount for Breakpoint {
    fn column_count() -> usize {
        // Position, log message, condition message, and hit condition message
        4 + BreakpointStateWrapper::column_count()
    }
}

impl sqlez::bindable::Bind for Breakpoint {
    fn bind(
        &self,
        statement: &sqlez::statement::Statement,
        start_index: i32,
    ) -> anyhow::Result<i32> {
        let next_index = statement.bind(&self.position, start_index)?;
        let next_index = statement.bind(&self.message, next_index)?;
        let next_index = statement.bind(&self.condition, next_index)?;
        let next_index = statement.bind(&self.hit_condition, next_index)?;
        statement.bind(
            &BreakpointStateWrapper(Cow::Borrowed(&self.state)),
            next_index,
        )
    }
}

impl Column for Breakpoint {
    fn column(statement: &mut Statement, start_index: i32) -> Result<(Self, i32)> {
        let position = statement
            .column_int(start_index)
            .with_context(|| format!("Failed to read BreakPoint at index {start_index}"))?
            as u32;
        let (message, next_index) = Option::<String>::column(statement, start_index + 1)?;
        let (condition, next_index) = Option::<String>::column(statement, next_index)?;
        let (hit_condition, next_index) = Option::<String>::column(statement, next_index)?;
        let (state, next_index) = BreakpointStateWrapper::column(statement, next_index)?;

        Ok((
            Breakpoint {
                position,
                message: message.map(Arc::from),
                condition: condition.map(Arc::from),
                hit_condition: hit_condition.map(Arc::from),
                state: state.0.into_owned(),
            },
            next_index,
        ))
    }
}

#[derive(Clone, Debug, PartialEq)]
struct SerializedPixels(gpui::Pixels);
impl sqlez::bindable::StaticColumnCount for SerializedPixels {}

impl sqlez::bindable::Bind for SerializedPixels {
    fn bind(
        &self,
        statement: &sqlez::statement::Statement,
        start_index: i32,
    ) -> anyhow::Result<i32> {
        let this: i32 = u32::from(self.0) as _;
        this.bind(statement, start_index)
    }
}

pub struct WorkspaceDb(ThreadSafeConnection);

impl Domain for WorkspaceDb {
    const NAME: &str = stringify!(WorkspaceDb);

    const MIGRATIONS: &[&str] = &[
        sql!(
            CREATE TABLE workspaces(
                workspace_id INTEGER PRIMARY KEY,
                workspace_location BLOB UNIQUE,
                dock_visible INTEGER, // Deprecated. Preserving so users can downgrade Zed.
                dock_anchor TEXT, // Deprecated. Preserving so users can downgrade Zed.
                dock_pane INTEGER, // Deprecated.  Preserving so users can downgrade Zed.
                left_sidebar_open INTEGER, // Boolean
                timestamp TEXT DEFAULT CURRENT_TIMESTAMP NOT NULL,
                FOREIGN KEY(dock_pane) REFERENCES panes(pane_id)
            ) STRICT;

            CREATE TABLE pane_groups(
                group_id INTEGER PRIMARY KEY,
                workspace_id INTEGER NOT NULL,
                parent_group_id INTEGER, // NULL indicates that this is a root node
                position INTEGER, // NULL indicates that this is a root node
                axis TEXT NOT NULL, // Enum: 'Vertical' / 'Horizontal'
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE,
                FOREIGN KEY(parent_group_id) REFERENCES pane_groups(group_id) ON DELETE CASCADE
            ) STRICT;

            CREATE TABLE panes(
                pane_id INTEGER PRIMARY KEY,
                workspace_id INTEGER NOT NULL,
                active INTEGER NOT NULL, // Boolean
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE
            ) STRICT;

            CREATE TABLE center_panes(
                pane_id INTEGER PRIMARY KEY,
                parent_group_id INTEGER, // NULL means that this is a root pane
                position INTEGER, // NULL means that this is a root pane
                FOREIGN KEY(pane_id) REFERENCES panes(pane_id)
                ON DELETE CASCADE,
                FOREIGN KEY(parent_group_id) REFERENCES pane_groups(group_id) ON DELETE CASCADE
            ) STRICT;

            CREATE TABLE items(
                item_id INTEGER NOT NULL, // This is the item's view id, so this is not unique
                workspace_id INTEGER NOT NULL,
                pane_id INTEGER NOT NULL,
                kind TEXT NOT NULL,
                position INTEGER NOT NULL,
                active INTEGER NOT NULL,
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE,
                FOREIGN KEY(pane_id) REFERENCES panes(pane_id)
                ON DELETE CASCADE,
                PRIMARY KEY(item_id, workspace_id)
            ) STRICT;
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN window_state TEXT;
            ALTER TABLE workspaces ADD COLUMN window_x REAL;
            ALTER TABLE workspaces ADD COLUMN window_y REAL;
            ALTER TABLE workspaces ADD COLUMN window_width REAL;
            ALTER TABLE workspaces ADD COLUMN window_height REAL;
            ALTER TABLE workspaces ADD COLUMN display BLOB;
        ),
        // Drop foreign key constraint from workspaces.dock_pane to panes table.
        sql!(
            CREATE TABLE workspaces_2(
                workspace_id INTEGER PRIMARY KEY,
                workspace_location BLOB UNIQUE,
                dock_visible INTEGER, // Deprecated. Preserving so users can downgrade Zed.
                dock_anchor TEXT, // Deprecated. Preserving so users can downgrade Zed.
                dock_pane INTEGER, // Deprecated.  Preserving so users can downgrade Zed.
                left_sidebar_open INTEGER, // Boolean
                timestamp TEXT DEFAULT CURRENT_TIMESTAMP NOT NULL,
                window_state TEXT,
                window_x REAL,
                window_y REAL,
                window_width REAL,
                window_height REAL,
                display BLOB
            ) STRICT;
            INSERT INTO workspaces_2 SELECT * FROM workspaces;
            DROP TABLE workspaces;
            ALTER TABLE workspaces_2 RENAME TO workspaces;
        ),
        // Add panels related information
        sql!(
            ALTER TABLE workspaces ADD COLUMN left_dock_visible INTEGER; //bool
            ALTER TABLE workspaces ADD COLUMN left_dock_active_panel TEXT;
            ALTER TABLE workspaces ADD COLUMN right_dock_visible INTEGER; //bool
            ALTER TABLE workspaces ADD COLUMN right_dock_active_panel TEXT;
            ALTER TABLE workspaces ADD COLUMN bottom_dock_visible INTEGER; //bool
            ALTER TABLE workspaces ADD COLUMN bottom_dock_active_panel TEXT;
        ),
        // Add panel zoom persistence
        sql!(
            ALTER TABLE workspaces ADD COLUMN left_dock_zoom INTEGER; //bool
            ALTER TABLE workspaces ADD COLUMN right_dock_zoom INTEGER; //bool
            ALTER TABLE workspaces ADD COLUMN bottom_dock_zoom INTEGER; //bool
        ),
        // Add pane group flex data
        sql!(
            ALTER TABLE pane_groups ADD COLUMN flexes TEXT;
        ),
        // Add fullscreen field to workspace
        // Deprecated, `WindowBounds` holds the fullscreen state now.
        // Preserving so users can downgrade Zed.
        sql!(
            ALTER TABLE workspaces ADD COLUMN fullscreen INTEGER; //bool
        ),
        // Add preview field to items
        sql!(
            ALTER TABLE items ADD COLUMN preview INTEGER; //bool
        ),
        // Add centered_layout field to workspace
        sql!(
            ALTER TABLE workspaces ADD COLUMN centered_layout INTEGER; //bool
        ),
        sql!(
            CREATE TABLE remote_projects (
                remote_project_id INTEGER NOT NULL UNIQUE,
                path TEXT,
                dev_server_name TEXT
            );
            ALTER TABLE workspaces ADD COLUMN remote_project_id INTEGER;
            ALTER TABLE workspaces RENAME COLUMN workspace_location TO local_paths;
        ),
        sql!(
            DROP TABLE remote_projects;
            CREATE TABLE dev_server_projects (
                id INTEGER NOT NULL UNIQUE,
                path TEXT,
                dev_server_name TEXT
            );
            ALTER TABLE workspaces DROP COLUMN remote_project_id;
            ALTER TABLE workspaces ADD COLUMN dev_server_project_id INTEGER;
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN local_paths_order BLOB;
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN session_id TEXT DEFAULT NULL;
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN window_id INTEGER DEFAULT NULL;
        ),
        sql!(
            ALTER TABLE panes ADD COLUMN pinned_count INTEGER DEFAULT 0;
        ),
        sql!(
            CREATE TABLE ssh_projects (
                id INTEGER PRIMARY KEY,
                host TEXT NOT NULL,
                port INTEGER,
                path TEXT NOT NULL,
                user TEXT
            );
            ALTER TABLE workspaces ADD COLUMN ssh_project_id INTEGER REFERENCES ssh_projects(id) ON DELETE CASCADE;
        ),
        sql!(
            ALTER TABLE ssh_projects RENAME COLUMN path TO paths;
        ),
        sql!(
            CREATE TABLE toolchains (
                workspace_id INTEGER,
                worktree_id INTEGER,
                language_name TEXT NOT NULL,
                name TEXT NOT NULL,
                path TEXT NOT NULL,
                PRIMARY KEY (workspace_id, worktree_id, language_name)
            );
        ),
        sql!(
            ALTER TABLE toolchains ADD COLUMN raw_json TEXT DEFAULT "{}";
        ),
        sql!(
            CREATE TABLE breakpoints (
                workspace_id INTEGER NOT NULL,
                path TEXT NOT NULL,
                breakpoint_location INTEGER NOT NULL,
                kind INTEGER NOT NULL,
                log_message TEXT,
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE
            );
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN local_paths_array TEXT;
            CREATE UNIQUE INDEX local_paths_array_uq ON workspaces(local_paths_array);
            ALTER TABLE workspaces ADD COLUMN local_paths_order_array TEXT;
        ),
        sql!(
            ALTER TABLE breakpoints ADD COLUMN state INTEGER DEFAULT(0) NOT NULL
        ),
        sql!(
            ALTER TABLE breakpoints DROP COLUMN kind
        ),
        sql!(ALTER TABLE toolchains ADD COLUMN relative_worktree_path TEXT DEFAULT "" NOT NULL),
        sql!(
            ALTER TABLE breakpoints ADD COLUMN condition TEXT;
            ALTER TABLE breakpoints ADD COLUMN hit_condition TEXT;
        ),
        sql!(CREATE TABLE toolchains2 (
            workspace_id INTEGER,
            worktree_id INTEGER,
            language_name TEXT NOT NULL,
            name TEXT NOT NULL,
            path TEXT NOT NULL,
            raw_json TEXT NOT NULL,
            relative_worktree_path TEXT NOT NULL,
            PRIMARY KEY (workspace_id, worktree_id, language_name, relative_worktree_path)) STRICT;
            INSERT INTO toolchains2
                SELECT * FROM toolchains;
            DROP TABLE toolchains;
            ALTER TABLE toolchains2 RENAME TO toolchains;
        ),
        sql!(
            CREATE TABLE ssh_connections (
                id INTEGER PRIMARY KEY,
                host TEXT NOT NULL,
                port INTEGER,
                user TEXT
            );

            INSERT INTO ssh_connections (host, port, user)
            SELECT DISTINCT host, port, user
            FROM ssh_projects;

            CREATE TABLE workspaces_2(
                workspace_id INTEGER PRIMARY KEY,
                paths TEXT,
                paths_order TEXT,
                ssh_connection_id INTEGER REFERENCES ssh_connections(id),
                timestamp TEXT DEFAULT CURRENT_TIMESTAMP NOT NULL,
                window_state TEXT,
                window_x REAL,
                window_y REAL,
                window_width REAL,
                window_height REAL,
                display BLOB,
                left_dock_visible INTEGER,
                left_dock_active_panel TEXT,
                right_dock_visible INTEGER,
                right_dock_active_panel TEXT,
                bottom_dock_visible INTEGER,
                bottom_dock_active_panel TEXT,
                left_dock_zoom INTEGER,
                right_dock_zoom INTEGER,
                bottom_dock_zoom INTEGER,
                fullscreen INTEGER,
                centered_layout INTEGER,
                session_id TEXT,
                window_id INTEGER
            ) STRICT;

            INSERT
            INTO workspaces_2
            SELECT
                workspaces.workspace_id,
                CASE
                    WHEN ssh_projects.id IS NOT NULL THEN ssh_projects.paths
                    ELSE
                        CASE
                            WHEN workspaces.local_paths_array IS NULL OR workspaces.local_paths_array = "" THEN
                                NULL
                            ELSE
                                replace(workspaces.local_paths_array, ',', CHAR(10))
                        END
                END as paths,

                CASE
                    WHEN ssh_projects.id IS NOT NULL THEN ""
                    ELSE workspaces.local_paths_order_array
                END as paths_order,

                CASE
                    WHEN ssh_projects.id IS NOT NULL THEN (
                        SELECT ssh_connections.id
                        FROM ssh_connections
                        WHERE
                            ssh_connections.host IS ssh_projects.host AND
                            ssh_connections.port IS ssh_projects.port AND
                            ssh_connections.user IS ssh_projects.user
                    )
                    ELSE NULL
                END as ssh_connection_id,

                workspaces.timestamp,
                workspaces.window_state,
                workspaces.window_x,
                workspaces.window_y,
                workspaces.window_width,
                workspaces.window_height,
                workspaces.display,
                workspaces.left_dock_visible,
                workspaces.left_dock_active_panel,
                workspaces.right_dock_visible,
                workspaces.right_dock_active_panel,
                workspaces.bottom_dock_visible,
                workspaces.bottom_dock_active_panel,
                workspaces.left_dock_zoom,
                workspaces.right_dock_zoom,
                workspaces.bottom_dock_zoom,
                workspaces.fullscreen,
                workspaces.centered_layout,
                workspaces.session_id,
                workspaces.window_id
            FROM
                workspaces LEFT JOIN
                ssh_projects ON
                workspaces.ssh_project_id = ssh_projects.id;

            DELETE FROM workspaces_2
            WHERE workspace_id NOT IN (
                SELECT MAX(workspace_id)
                FROM workspaces_2
                GROUP BY ssh_connection_id, paths
            );

            DROP TABLE ssh_projects;
            DROP TABLE workspaces;
            ALTER TABLE workspaces_2 RENAME TO workspaces;

            CREATE UNIQUE INDEX ix_workspaces_location ON workspaces(ssh_connection_id, paths);
        ),
        // Fix any data from when workspaces.paths were briefly encoded as JSON arrays
        sql!(
            UPDATE workspaces
            SET paths = CASE
                WHEN substr(paths, 1, 2) = '[' || '"' AND substr(paths, -2, 2) = '"' || ']' THEN
                    replace(
                        substr(paths, 3, length(paths) - 4),
                        '"' || ',' || '"',
                        CHAR(10)
                    )
                ELSE
                    replace(paths, ',', CHAR(10))
            END
            WHERE paths IS NOT NULL
        ),
        sql!(
            CREATE TABLE remote_connections(
                id INTEGER PRIMARY KEY,
                kind TEXT NOT NULL,
                host TEXT,
                port INTEGER,
                user TEXT,
                distro TEXT
            );

            CREATE TABLE workspaces_2(
                workspace_id INTEGER PRIMARY KEY,
                paths TEXT,
                paths_order TEXT,
                remote_connection_id INTEGER REFERENCES remote_connections(id),
                timestamp TEXT DEFAULT CURRENT_TIMESTAMP NOT NULL,
                window_state TEXT,
                window_x REAL,
                window_y REAL,
                window_width REAL,
                window_height REAL,
                display BLOB,
                left_dock_visible INTEGER,
                left_dock_active_panel TEXT,
                right_dock_visible INTEGER,
                right_dock_active_panel TEXT,
                bottom_dock_visible INTEGER,
                bottom_dock_active_panel TEXT,
                left_dock_zoom INTEGER,
                right_dock_zoom INTEGER,
                bottom_dock_zoom INTEGER,
                fullscreen INTEGER,
                centered_layout INTEGER,
                session_id TEXT,
                window_id INTEGER
            ) STRICT;

            INSERT INTO remote_connections
            SELECT
                id,
                "ssh" as kind,
                host,
                port,
                user,
                NULL as distro
            FROM ssh_connections;

            INSERT
            INTO workspaces_2
            SELECT
                workspace_id,
                paths,
                paths_order,
                ssh_connection_id as remote_connection_id,
                timestamp,
                window_state,
                window_x,
                window_y,
                window_width,
                window_height,
                display,
                left_dock_visible,
                left_dock_active_panel,
                right_dock_visible,
                right_dock_active_panel,
                bottom_dock_visible,
                bottom_dock_active_panel,
                left_dock_zoom,
                right_dock_zoom,
                bottom_dock_zoom,
                fullscreen,
                centered_layout,
                session_id,
                window_id
            FROM
                workspaces;

            DROP TABLE workspaces;
            ALTER TABLE workspaces_2 RENAME TO workspaces;

            CREATE UNIQUE INDEX ix_workspaces_location ON workspaces(remote_connection_id, paths);
        ),
        sql!(CREATE TABLE user_toolchains (
            remote_connection_id INTEGER,
            workspace_id INTEGER NOT NULL,
            worktree_id INTEGER NOT NULL,
            relative_worktree_path TEXT NOT NULL,
            language_name TEXT NOT NULL,
            name TEXT NOT NULL,
            path TEXT NOT NULL,
            raw_json TEXT NOT NULL,

            PRIMARY KEY (workspace_id, worktree_id, relative_worktree_path, language_name, name, path, raw_json)
        ) STRICT;),
        sql!(
            DROP TABLE ssh_connections;
        ),
        sql!(
            ALTER TABLE remote_connections ADD COLUMN name TEXT;
            ALTER TABLE remote_connections ADD COLUMN container_id TEXT;
        ),
        sql!(
            CREATE TABLE IF NOT EXISTS trusted_worktrees (
                trust_id INTEGER PRIMARY KEY AUTOINCREMENT,
                absolute_path TEXT,
                user_name TEXT,
                host_name TEXT
            ) STRICT;
        ),
        sql!(CREATE TABLE toolchains2 (
            workspace_id INTEGER,
            worktree_root_path TEXT NOT NULL,
            language_name TEXT NOT NULL,
            name TEXT NOT NULL,
            path TEXT NOT NULL,
            raw_json TEXT NOT NULL,
            relative_worktree_path TEXT NOT NULL,
            PRIMARY KEY (workspace_id, worktree_root_path, language_name, relative_worktree_path)) STRICT;
            INSERT OR REPLACE INTO toolchains2
                // The `instr(paths, '\n') = 0` part allows us to find all
                // workspaces that have a single worktree, as `\n` is used as a
                // separator when serializing the workspace paths, so if no `\n` is
                // found, we know we have a single worktree.
                SELECT toolchains.workspace_id, paths, language_name, name, path, raw_json, relative_worktree_path FROM toolchains INNER JOIN workspaces ON toolchains.workspace_id = workspaces.workspace_id AND instr(paths, '\n') = 0;
            DROP TABLE toolchains;
            ALTER TABLE toolchains2 RENAME TO toolchains;
        ),
        sql!(CREATE TABLE user_toolchains2 (
            remote_connection_id INTEGER,
            workspace_id INTEGER NOT NULL,
            worktree_root_path TEXT NOT NULL,
            relative_worktree_path TEXT NOT NULL,
            language_name TEXT NOT NULL,
            name TEXT NOT NULL,
            path TEXT NOT NULL,
            raw_json TEXT NOT NULL,

            PRIMARY KEY (workspace_id, worktree_root_path, relative_worktree_path, language_name, name, path, raw_json)) STRICT;
            INSERT OR REPLACE INTO user_toolchains2
                // The `instr(paths, '\n') = 0` part allows us to find all
                // workspaces that have a single worktree, as `\n` is used as a
                // separator when serializing the workspace paths, so if no `\n` is
                // found, we know we have a single worktree.
                SELECT user_toolchains.remote_connection_id, user_toolchains.workspace_id, paths, relative_worktree_path, language_name, name, path, raw_json  FROM user_toolchains INNER JOIN workspaces ON user_toolchains.workspace_id = workspaces.workspace_id AND instr(paths, '\n') = 0;
            DROP TABLE user_toolchains;
            ALTER TABLE user_toolchains2 RENAME TO user_toolchains;
        ),
        sql!(
            ALTER TABLE remote_connections ADD COLUMN use_podman BOOLEAN;
        ),
        sql!(
            ALTER TABLE remote_connections ADD COLUMN remote_env TEXT;
        ),
        sql!(
            CREATE TABLE bookmarks (
                workspace_id INTEGER NOT NULL,
                path TEXT NOT NULL,
                row INTEGER NOT NULL,
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE
            );
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN identity_paths TEXT;
            ALTER TABLE workspaces ADD COLUMN identity_paths_order TEXT;
        ),
        sql!(
            ALTER TABLE bookmarks ADD COLUMN label TEXT NOT NULL DEFAULT "";
        ),
        sql!(
            CREATE TABLE recent_navigation_history (
                workspace_id INTEGER NOT NULL,
                path BLOB NOT NULL,
                position INTEGER NOT NULL,
                PRIMARY KEY (workspace_id, path),
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
                ON UPDATE CASCADE
            ) STRICT;
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN native_window_state BLOB;
        ),
        sql!(
            CREATE TABLE restoring_windows (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                state TEXT NOT NULL
            ) STRICT;
            ALTER TABLE workspaces ADD COLUMN restoring_window_id INTEGER
                REFERENCES restoring_windows(id);
        ),
        sql!(
            DROP INDEX ix_workspaces_location;
            CREATE INDEX ix_workspaces_location ON workspaces(remote_connection_id, paths);
        ),
        sql!(
            ALTER TABLE workspaces ADD COLUMN in_recent_history INTEGER NOT NULL DEFAULT 1;
        ),
    ];

    // Allow recovering from bad migration that was initially shipped to nightly
    // when introducing the ssh_connections table.
    fn should_allow_migration_change(_index: usize, old: &str, new: &str) -> bool {
        old.starts_with("CREATE TABLE ssh_connections")
            && new.starts_with("CREATE TABLE ssh_connections")
    }
}

db::static_connection!(WorkspaceDb, [KeyValueStore]);

impl WorkspaceDb {
    /// Returns a serialized workspace for the given worktree_roots. If the passed array
    /// is empty, the most recent workspace is returned instead. If no workspace for the
    /// passed roots is stored, returns none.
    pub(crate) fn workspace_for_roots<P: AsRef<Path>>(
        &self,
        worktree_roots: &[P],
    ) -> Option<SerializedWorkspace> {
        self.workspace_for_roots_internal(worktree_roots, None)
    }

    pub(crate) fn remote_workspace_for_roots<P: AsRef<Path>>(
        &self,
        worktree_roots: &[P],
        remote_project_id: RemoteConnectionId,
    ) -> Option<SerializedWorkspace> {
        self.workspace_for_roots_internal(worktree_roots, Some(remote_project_id))
    }

    pub(crate) fn workspace_id_for_roots_in_window<P: AsRef<Path>>(
        &self,
        worktree_roots: &[P],
        remote_connection_id: Option<RemoteConnectionId>,
        binding: &WorkspaceBinding,
    ) -> Result<Option<WorkspaceId>> {
        let paths = PathList::new(worktree_roots);
        if paths.is_empty() && remote_connection_id.is_none() {
            return Ok(None);
        }
        self.select_row_bound(sql!(
            SELECT workspace_id FROM workspaces
            WHERE paths IS ?1 AND remote_connection_id IS ?2 AND session_id = ?3
                AND ((restoring_window_id IS NULL AND window_id = ?4)
                    OR restoring_window_id = ?5)
            ORDER BY timestamp DESC, workspace_id DESC LIMIT 1
        ))?((
            paths.serialize().paths,
            remote_connection_id.map(|id| id.0),
            binding.0.as_deref(),
            binding.1,
            binding.2,
        ))
    }

    pub(crate) fn workspace_for_roots_internal<P: AsRef<Path>>(
        &self,
        worktree_roots: &[P],
        remote_connection_id: Option<RemoteConnectionId>,
    ) -> Option<SerializedWorkspace> {
        // paths are sorted before db interactions to ensure that the order of the paths
        // doesn't affect the workspace selection for existing workspaces
        let root_paths = PathList::new(worktree_roots);

        // Empty workspaces cannot be matched by paths (all empty workspaces have paths = "").
        // They should only be restored via workspace_for_id during session restoration.
        if root_paths.is_empty() && remote_connection_id.is_none() {
            return None;
        }

        let workspace_id = self
            .select_row_bound::<_, WorkspaceId>(sql!(
                SELECT workspace_id FROM workspaces
                WHERE paths IS ? AND remote_connection_id IS ?
                ORDER BY timestamp DESC, workspace_id DESC
                LIMIT 1
            ))
            .and_then(|mut prepared_statement| {
                (prepared_statement)((
                    root_paths.serialize().paths,
                    remote_connection_id.map(|id| id.0 as i32),
                ))
            })
            .context("No workspaces found")
            .warn_on_err()
            .flatten()?;

        let mut workspace = self.workspace_for_id(workspace_id)?;
        workspace.session_id = None;
        workspace.restoring_window_id = None;
        Some(workspace)
    }

    /// Returns the workspace with the given ID, loading all associated data.
    pub(crate) fn workspace_for_id(
        &self,
        workspace_id: WorkspaceId,
    ) -> Option<SerializedWorkspace> {
        let (
            paths,
            paths_order,
            identity_paths,
            identity_paths_order,
            window_bounds,
            display,
            centered_layout,
            docks,
            (window_id, session_id, restoring_window_id),
            remote_connection_id,
        ): (
            String,
            String,
            Option<String>,
            Option<String>,
            Option<SerializedWindowBounds>,
            Option<Uuid>,
            Option<bool>,
            DockStructure,
            (Option<u64>, Option<String>, Option<i64>),
            Option<i32>,
        ) = self
            .select_row_bound(sql! {
                SELECT
                    paths,
                    paths_order,
                    identity_paths,
                    identity_paths_order,
                    window_state,
                    window_x,
                    window_y,
                    window_width,
                    window_height,
                    display,
                    centered_layout,
                    left_dock_visible,
                    left_dock_active_panel,
                    left_dock_zoom,
                    right_dock_visible,
                    right_dock_active_panel,
                    right_dock_zoom,
                    bottom_dock_visible,
                    bottom_dock_active_panel,
                    bottom_dock_zoom,
                    window_id,
                    session_id,
                    restoring_window_id,
                    remote_connection_id
                FROM workspaces
                WHERE workspace_id = ?
            })
            .and_then(|mut prepared_statement| (prepared_statement)(workspace_id))
            .context("No workspace found for id")
            .warn_on_err()
            .flatten()?;

        let paths = PathList::deserialize(&SerializedPathList {
            paths,
            order: paths_order,
        });
        let identity_paths = identity_paths.map(|paths| {
            PathList::deserialize(&SerializedPathList {
                paths,
                order: identity_paths_order.unwrap_or_default(),
            })
        });

        let remote_connection_id = remote_connection_id.map(|id| RemoteConnectionId(id as u64));
        let remote_connection_options = if let Some(remote_connection_id) = remote_connection_id {
            self.remote_connection(remote_connection_id)
                .context("Get remote connection")
                .log_err()
        } else {
            None
        };

        Some(SerializedWorkspace {
            id: workspace_id,
            location: match remote_connection_options {
                Some(options) => SerializedWorkspaceLocation::Remote(options),
                None => SerializedWorkspaceLocation::Local,
            },
            paths,
            identity_paths,
            center_group: self
                .get_center_pane_group(workspace_id)
                .context("Getting center group")
                .log_err()?,
            window_bounds,
            centered_layout: centered_layout.unwrap_or(false),
            display,
            docks,
            session_id,
            bookmarks: self.bookmarks(workspace_id),
            breakpoints: self.breakpoints(workspace_id),
            window_id,
            user_toolchains: self.user_toolchains(workspace_id, remote_connection_id),
            restoring_window_id,
            recent_navigation_history: self.recent_navigation_history(workspace_id),
        })
    }

    fn recent_navigation_history(&self, workspace_id: WorkspaceId) -> Vec<PathBuf> {
        self.select_bound(sql!(
            SELECT path
            FROM recent_navigation_history
            WHERE workspace_id = ?
            ORDER BY position
        ))
        .and_then(|mut statement| statement(workspace_id))
        .context("Loading recent navigation history")
        .log_err()
        .unwrap_or_default()
    }

    fn bookmarks(&self, workspace_id: WorkspaceId) -> BTreeMap<Arc<Path>, Vec<SerializedBookmark>> {
        let bookmarks: Result<Vec<(PathBuf, Bookmark)>> = self
            .select_bound(sql! {
                SELECT path, row, label
                FROM bookmarks
                WHERE workspace_id = ?
                ORDER BY path, row
            })
            .and_then(|mut prepared_statement| (prepared_statement)(workspace_id));

        match bookmarks {
            Ok(bookmarks) => {
                if bookmarks.is_empty() {
                    log::debug!("Bookmarks are empty after querying database for them");
                }

                let mut map: BTreeMap<_, Vec<_>> = BTreeMap::default();

                for (path, bookmark) in bookmarks {
                    let path: Arc<Path> = path.into();
                    map.entry(path.clone())
                        .or_default()
                        .push(SerializedBookmark {
                            row: bookmark.row,
                            label: bookmark.label,
                        })
                }

                map
            }
            Err(e) => {
                log::error!("Failed to load bookmarks: {}", e);
                BTreeMap::default()
            }
        }
    }

    fn breakpoints(&self, workspace_id: WorkspaceId) -> BTreeMap<Arc<Path>, Vec<SourceBreakpoint>> {
        let breakpoints: Result<Vec<(PathBuf, Breakpoint)>> = self
            .select_bound(sql! {
                SELECT path, breakpoint_location, log_message, condition, hit_condition, state
                FROM breakpoints
                WHERE workspace_id = ?
            })
            .and_then(|mut prepared_statement| (prepared_statement)(workspace_id));

        match breakpoints {
            Ok(bp) => {
                if bp.is_empty() {
                    log::debug!("Breakpoints are empty after querying database for them");
                }

                let mut map: BTreeMap<Arc<Path>, Vec<SourceBreakpoint>> = Default::default();

                for (path, breakpoint) in bp {
                    let path: Arc<Path> = path.into();
                    map.entry(path.clone()).or_default().push(SourceBreakpoint {
                        row: breakpoint.position,
                        path,
                        message: breakpoint.message,
                        condition: breakpoint.condition,
                        hit_condition: breakpoint.hit_condition,
                        state: breakpoint.state,
                    });
                }

                for (path, bps) in map.iter() {
                    log::info!(
                        "Got {} breakpoints from database at path: {}",
                        bps.len(),
                        path.to_string_lossy()
                    );
                }

                map
            }
            Err(msg) => {
                log::error!("Breakpoints query failed with msg: {msg}");
                Default::default()
            }
        }
    }

    fn user_toolchains(
        &self,
        workspace_id: WorkspaceId,
        remote_connection_id: Option<RemoteConnectionId>,
    ) -> BTreeMap<ToolchainScope, IndexSet<Toolchain>> {
        type RowKind = (WorkspaceId, String, String, String, String, String, String);

        let toolchains: Vec<RowKind> = self
            .select_bound(sql! {
                SELECT workspace_id, worktree_root_path, relative_worktree_path,
                language_name, name, path, raw_json
                FROM user_toolchains WHERE remote_connection_id IS ?1 AND (
                      workspace_id IN (0, ?2)
                )
            })
            .and_then(|mut statement| {
                (statement)((remote_connection_id.map(|id| id.0), workspace_id))
            })
            .unwrap_or_default();
        let mut ret = BTreeMap::<_, IndexSet<_>>::default();

        for (
            _workspace_id,
            worktree_root_path,
            relative_worktree_path,
            language_name,
            name,
            path,
            raw_json,
        ) in toolchains
        {
            // INTEGER's that are primary keys (like workspace ids, remote connection ids and such) start at 1, so we're safe to
            let scope = if _workspace_id == WorkspaceId(0) {
                debug_assert_eq!(worktree_root_path, String::default());
                debug_assert_eq!(relative_worktree_path, String::default());
                ToolchainScope::Global
            } else {
                debug_assert_eq!(workspace_id, _workspace_id);
                debug_assert_eq!(
                    worktree_root_path == String::default(),
                    relative_worktree_path == String::default()
                );

                let Some(relative_path) = RelPath::from_unix_str(&relative_worktree_path).log_err()
                else {
                    continue;
                };
                if worktree_root_path != String::default()
                    && relative_worktree_path != String::default()
                {
                    ToolchainScope::Subproject(
                        Arc::from(worktree_root_path.as_ref()),
                        relative_path.into(),
                    )
                } else {
                    ToolchainScope::Project
                }
            };
            let Ok(as_json) = serde_json::from_str(&raw_json) else {
                continue;
            };
            let toolchain = Toolchain {
                name: SharedString::from(name),
                path: SharedString::from(path),
                language_name: LanguageName::from_proto(language_name),
                as_json,
            };
            ret.entry(scope).or_default().insert(toolchain);
        }

        ret
    }

    #[cfg(test)]
    pub(crate) async fn save_workspace(&self, workspace: SerializedWorkspace) -> Result<()> {
        self.write(Self::prepare_save_workspace(workspace)).await
    }

    pub(crate) async fn save_snapshot(
        &self,
        expected_binding: Option<(WorkspaceId, WorkspaceBinding)>,
        writes: Vec<db::Write>,
    ) -> Result<()> {
        self.write(move |connection| {
            connection.with_savepoint("workspace_snapshot", || {
                if let Some((workspace_id, expected)) = expected_binding {
                    let binding = connection.select_row_bound::<_, WorkspaceBinding>(sql!(
                        SELECT session_id, window_id, restoring_window_id
                        FROM workspaces WHERE workspace_id = ?
                    ))?(workspace_id)?;
                    anyhow::ensure!(
                        binding.is_some_and(|binding| {
                            binding.0 == expected.0 && binding.1 == expected.1
                        }),
                        WorkspaceOwnershipChanged
                    );
                }
                for write in writes {
                    write(connection)?;
                }
                Ok(())
            })
        })
        .await
    }

    pub(crate) fn prepare_save_workspace(workspace: SerializedWorkspace) -> db::Write {
        let paths = workspace.paths.serialize();
        let identity_paths = workspace.identity_paths.map(|paths| paths.serialize());
        log::debug!("Saving workspace at location: {:?}", workspace.location);
        Box::new(move |conn| {
            conn.with_savepoint("update_worktrees", || {
                let remote_connection_id = match workspace.location.clone() {
                    SerializedWorkspaceLocation::Local => None,
                    SerializedWorkspaceLocation::Remote(connection_options) => {
                        Some(Self::get_or_create_remote_connection_internal(
                            conn,
                            connection_options
                        )?.0)
                    }
                };

                // Clear out panes and pane_groups
                conn.exec_bound(sql!(
                    DELETE FROM pane_groups WHERE workspace_id = ?1;
                    DELETE FROM panes WHERE workspace_id = ?1;))?(workspace.id)
                    .context("Clearing old panes")?;

                conn.exec_bound(
                    sql!(
                        DELETE FROM bookmarks WHERE workspace_id = ?1;
                    )
                )?(workspace.id).context("Clearing old bookmarks")?;

                for (path, bookmarks) in workspace.bookmarks {
                    for bookmark in bookmarks {
                        conn.exec_bound(sql!(
                            INSERT INTO bookmarks (workspace_id, path, row, label)
                            VALUES (?1, ?2, ?3, ?4);
                        ))?((workspace.id, path.as_ref(), bookmark.row, bookmark.label)).context("Inserting bookmark")?;
                    }
                }

                conn.exec_bound(
                    sql!(
                        DELETE FROM breakpoints WHERE workspace_id = ?1;
                    )
                )?(workspace.id).context("Clearing old breakpoints")?;

                for (path, breakpoints) in workspace.breakpoints {
                    for bp in breakpoints {
                        let state = BreakpointStateWrapper::from(bp.state);
                        match conn.exec_bound(sql!(
                            INSERT INTO breakpoints (workspace_id, path, breakpoint_location,  log_message, condition, hit_condition, state)
                            VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7);))?

                        ((
                            workspace.id,
                            path.as_ref(),
                            bp.row,
                            bp.message,
                            bp.condition,
                            bp.hit_condition,
                            state,
                        )) {
                            Ok(_) => {
                                log::debug!("Stored breakpoint at row: {} in path: {}", bp.row, path.to_string_lossy())
                            }
                            Err(err) => {
                                log::error!("{err}");
                                continue;
                            }
                        }
                    }
                }

                conn.exec_bound(
                    sql!(
                        DELETE FROM user_toolchains WHERE workspace_id = ?1;
                    )
                )?(workspace.id).context("Clearing old user toolchains")?;

                for (scope, toolchains) in workspace.user_toolchains {
                    for toolchain in toolchains {
                        let query = sql!(INSERT OR REPLACE INTO user_toolchains(remote_connection_id, workspace_id, worktree_root_path, relative_worktree_path, language_name, name, path, raw_json) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8));
                        let (workspace_id, worktree_root_path, relative_worktree_path) = match scope {
                            ToolchainScope::Subproject(ref worktree_root_path, ref path) => (Some(workspace.id), Some(worktree_root_path.to_string_lossy().into_owned()), Some(path.as_unix_str().to_owned())),
                            ToolchainScope::Project => (Some(workspace.id), None, None),
                            ToolchainScope::Global => (None, None, None),
                        };
                        let args = (remote_connection_id, workspace_id.unwrap_or(WorkspaceId(0)), worktree_root_path.unwrap_or_default(), relative_worktree_path.unwrap_or_default(),
                        toolchain.language_name.as_ref().to_owned(), toolchain.name.to_string(), toolchain.path.to_string(), toolchain.as_json.to_string());
                        if let Err(err) = conn.exec_bound(query)?(args) {
                            log::error!("{err}");
                            continue;
                        }
                    }
                }


                // Upsert
                let query = sql!(
                    INSERT INTO workspaces(
                        workspace_id,
                        paths,
                        paths_order,
                        identity_paths,
                        identity_paths_order,
                        remote_connection_id,
                        left_dock_visible,
                        left_dock_active_panel,
                        left_dock_zoom,
                        right_dock_visible,
                        right_dock_active_panel,
                        right_dock_zoom,
                        bottom_dock_visible,
                        bottom_dock_active_panel,
                        bottom_dock_zoom,
                        session_id,
                        window_id,
                        timestamp
                    )
                    VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, CURRENT_TIMESTAMP)
                    ON CONFLICT DO
                    UPDATE SET
                        paths = ?2,
                        paths_order = ?3,
                        identity_paths = ?4,
                        identity_paths_order = ?5,
                        remote_connection_id = ?6,
                        left_dock_visible = ?7,
                        left_dock_active_panel = ?8,
                        left_dock_zoom = ?9,
                        right_dock_visible = ?10,
                        right_dock_active_panel = ?11,
                        right_dock_zoom = ?12,
                        bottom_dock_visible = ?13,
                        bottom_dock_active_panel = ?14,
                        bottom_dock_zoom = ?15,
                        restoring_window_id = CASE WHEN session_id IS ?16 AND restoring_window_id = ?18
                            THEN restoring_window_id END,
                        session_id = ?16,
                        window_id = ?17,
                        timestamp = CURRENT_TIMESTAMP
                );
                let mut prepared_query = conn.exec_bound(query)?;
                let args = (
                    workspace.id,
                    paths.paths.clone(),
                    paths.order.clone(),
                    identity_paths.as_ref().map(|paths| paths.paths.clone()),
                    identity_paths.as_ref().map(|paths| paths.order.clone()),
                    remote_connection_id,
                    workspace.docks,
                    workspace.session_id,
                    workspace.window_id,
                    workspace.restoring_window_id,
                );

                prepared_query(args).context("Updating workspace")?;

                conn.exec_bound(sql!(
                    DELETE FROM recent_navigation_history WHERE workspace_id = ?;
                ))?(workspace.id)
                .context("Clearing recent navigation history")?;

                let mut insert_recent_path = conn.exec_bound(sql!(
                    INSERT INTO recent_navigation_history(workspace_id, path, position)
                    VALUES (?, ?, ?);
                ))?;
                for (position, path) in workspace.recent_navigation_history.iter().enumerate() {
                    insert_recent_path((workspace.id, path.as_path(), position))
                        .context("Inserting recent navigation history")?;
                }

                // Save center pane group
                Self::save_pane_group(conn, workspace.id, &workspace.center_group, None)
                    .context("save pane group in save workspace")?;

                Ok(())
            })
        })
    }

    pub(crate) async fn get_or_create_remote_connection(
        &self,
        options: RemoteConnectionOptions,
    ) -> Result<RemoteConnectionId> {
        self.write(move |conn| Self::get_or_create_remote_connection_internal(conn, options))
            .await
    }

    fn get_or_create_remote_connection_internal(
        this: &Connection,
        options: RemoteConnectionOptions,
    ) -> Result<RemoteConnectionId> {
        let identity = remote_connection_identity(&options);
        let kind;
        let user: Option<String>;
        let mut host = None;
        let mut port = None;
        let mut distro = None;
        let mut name = None;
        let mut container_id = None;
        let mut use_podman = None;
        let mut remote_env = None;

        match identity {
            RemoteConnectionIdentity::Ssh {
                host: identity_host,
                username,
                port: identity_port,
            } => {
                kind = RemoteConnectionKind::Ssh;
                host = Some(identity_host);
                port = identity_port;
                user = username;
            }
            RemoteConnectionIdentity::Wsl {
                distro_name,
                user: identity_user,
            } => {
                kind = RemoteConnectionKind::Wsl;
                distro = Some(distro_name);
                user = identity_user;
            }
            RemoteConnectionIdentity::Docker {
                container_id: identity_container_id,
                name: identity_name,
                remote_user,
            } => {
                kind = RemoteConnectionKind::Docker;
                container_id = Some(identity_container_id);
                name = Some(identity_name);
                user = Some(remote_user);
            }
            #[cfg(any(test, feature = "test-support"))]
            RemoteConnectionIdentity::Mock { id } => {
                kind = RemoteConnectionKind::Ssh;
                host = Some(format!("mock-{}", id));
                user = Some(format!("mock-user-{}", id));
            }
        }

        if let RemoteConnectionOptions::Docker(options) = options {
            use_podman = Some(options.use_podman);
            remote_env = serde_json::to_string(&options.remote_env).ok();
        }

        Self::get_or_create_remote_connection_query(
            this,
            kind,
            host,
            port,
            user,
            distro,
            name,
            container_id,
            use_podman,
            remote_env,
        )
    }

    fn get_or_create_remote_connection_query(
        this: &Connection,
        kind: RemoteConnectionKind,
        host: Option<String>,
        port: Option<u16>,
        user: Option<String>,
        distro: Option<String>,
        name: Option<String>,
        container_id: Option<String>,
        use_podman: Option<bool>,
        remote_env: Option<String>,
    ) -> Result<RemoteConnectionId> {
        if let Some(id) = this.select_row_bound(sql!(
            SELECT id
            FROM remote_connections
            WHERE
                kind IS ? AND
                host IS ? AND
                port IS ? AND
                user IS ? AND
                distro IS ? AND
                name IS ? AND
                container_id IS ?
            LIMIT 1
        ))?((
            kind.serialize(),
            host.clone(),
            port,
            user.clone(),
            distro.clone(),
            name.clone(),
            container_id.clone(),
        ))? {
            Ok(RemoteConnectionId(id))
        } else {
            let id = this.select_row_bound(sql!(
                INSERT INTO remote_connections (
                    kind,
                    host,
                    port,
                    user,
                    distro,
                    name,
                    container_id,
                    use_podman,
                    remote_env
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9)
                RETURNING id
            ))?((
                kind.serialize(),
                host,
                port,
                user,
                distro,
                name,
                container_id,
                use_podman,
                remote_env,
            ))?
            .context("failed to insert remote project")?;
            Ok(RemoteConnectionId(id))
        }
    }

    query! {
        pub async fn next_id() -> Result<WorkspaceId> {
            INSERT INTO workspaces DEFAULT VALUES RETURNING workspace_id
        }
    }

    fn recent_workspaces(
        &self,
    ) -> Result<
        Vec<(
            WorkspaceId,
            PathList,
            Option<PathList>,
            Option<RemoteConnectionId>,
            Option<String>,
            DateTime<Utc>,
        )>,
    > {
        Ok(self
            .recent_workspaces_query()?
            .into_iter()
            .map(
                |(
                    id,
                    paths,
                    order,
                    identity_paths,
                    identity_paths_order,
                    remote_connection_id,
                    session_id,
                    timestamp,
                )| {
                    (
                        id,
                        PathList::deserialize(&SerializedPathList { paths, order }),
                        identity_paths.map(|paths| {
                            PathList::deserialize(&SerializedPathList {
                                paths,
                                order: identity_paths_order.unwrap_or_default(),
                            })
                        }),
                        remote_connection_id.map(RemoteConnectionId),
                        session_id,
                        parse_timestamp(&timestamp),
                    )
                },
            )
            .collect())
    }

    query! {
        fn recent_workspaces_query() -> Result<Vec<(WorkspaceId, String, String, Option<String>, Option<String>, Option<u64>, Option<String>, String)>> {
            SELECT workspace_id, paths, paths_order, identity_paths, identity_paths_order, remote_connection_id, session_id, timestamp
            FROM workspaces
            WHERE in_recent_history AND (paths IS NOT NULL OR remote_connection_id IS NOT NULL)
            ORDER BY timestamp DESC
        }
    }

    pub(crate) fn session_workspaces(
        &self,
        session_id: String,
    ) -> Result<
        Vec<(
            WorkspaceId,
            PathList,
            Option<u64>,
            Option<RemoteConnectionId>,
        )>,
    > {
        Ok(self
            .session_workspaces_query(session_id)?
            .into_iter()
            .map(
                |(workspace_id, paths, order, window_id, remote_connection_id)| {
                    (
                        WorkspaceId(workspace_id),
                        PathList::deserialize(&SerializedPathList { paths, order }),
                        window_id,
                        remote_connection_id.map(RemoteConnectionId),
                    )
                },
            )
            .collect())
    }

    query! {
        fn session_workspaces_query(session_id: String) -> Result<Vec<(i64, String, String, Option<u64>, Option<u64>)>> {
            SELECT workspace_id, paths, paths_order, window_id, remote_connection_id
            FROM workspaces
            WHERE session_id = ?1
            ORDER BY timestamp DESC
        }
    }

    query! {
        pub fn breakpoints_for_file(workspace_id: WorkspaceId, file_path: &Path) -> Result<Vec<Breakpoint>> {
            SELECT breakpoint_location
            FROM breakpoints
            WHERE  workspace_id= ?1 AND path = ?2
        }
    }

    query! {
        pub fn clear_breakpoints(file_path: &Path) -> Result<()> {
            DELETE FROM breakpoints
            WHERE file_path = ?2
        }
    }

    fn remote_connections(&self) -> Result<HashMap<RemoteConnectionId, RemoteConnectionOptions>> {
        Ok(self.select(sql!(
            SELECT
                id, kind, host, port, user, distro, container_id, name, use_podman, remote_env
            FROM
                remote_connections
        ))?()?
        .into_iter()
        .filter_map(
            |(id, kind, host, port, user, distro, container_id, name, use_podman, remote_env)| {
                Some((
                    RemoteConnectionId(id),
                    Self::remote_connection_from_row(
                        kind,
                        host,
                        port,
                        user,
                        distro,
                        container_id,
                        name,
                        use_podman,
                        remote_env,
                    )?,
                ))
            },
        )
        .collect())
    }

    pub(crate) fn remote_connection(
        &self,
        id: RemoteConnectionId,
    ) -> Result<RemoteConnectionOptions> {
        let (kind, host, port, user, distro, container_id, name, use_podman, remote_env) =
            self.select_row_bound(sql!(
                SELECT kind, host, port, user, distro, container_id, name, use_podman, remote_env
                FROM remote_connections
                WHERE id = ?
            ))?(id.0)?
            .context("no such remote connection")?;
        Self::remote_connection_from_row(
            kind,
            host,
            port,
            user,
            distro,
            container_id,
            name,
            use_podman,
            remote_env,
        )
        .context("invalid remote_connection row")
    }

    fn remote_connection_from_row(
        kind: String,
        host: Option<String>,
        port: Option<u16>,
        user: Option<String>,
        distro: Option<String>,
        container_id: Option<String>,
        name: Option<String>,
        use_podman: Option<bool>,
        remote_env: Option<String>,
    ) -> Option<RemoteConnectionOptions> {
        match RemoteConnectionKind::deserialize(&kind)? {
            RemoteConnectionKind::Wsl => Some(RemoteConnectionOptions::Wsl(WslConnectionOptions {
                distro_name: distro?,
                user: user,
            })),
            RemoteConnectionKind::Ssh => Some(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host?.into(),
                port,
                username: user,
                ..Default::default()
            })),
            RemoteConnectionKind::Docker => {
                let remote_env: BTreeMap<String, String> =
                    serde_json::from_str(&remote_env?).ok()?;
                Some(RemoteConnectionOptions::Docker(DockerConnectionOptions {
                    container_id: container_id?,
                    name: name?,
                    remote_user: user?,
                    upload_binary_over_docker_exec: false,
                    use_podman: use_podman?,
                    remote_env,
                }))
            }
        }
    }

    query! {
        pub async fn delete_workspace_by_id(id: WorkspaceId) -> Result<()> {
            DELETE FROM workspaces
            WHERE workspace_id IS ?
        }
    }

    async fn all_paths_exist(paths: &[PathBuf], fs: &dyn Fs, require_directory: bool) -> bool {
        let mut any_dir = false;
        for path in paths {
            match fs.metadata(path).await.ok().flatten() {
                None => return false,
                Some(meta) => {
                    if meta.is_dir {
                        any_dir = true;
                    }
                }
            }
        }
        !require_directory || any_dir
    }

    // Returns the raw recent workspace history. Scratch workspaces (no paths) are filtered
    // out because they are restored separately by `last_session_workspace_locations`.
    pub async fn recent_project_workspaces_ungrouped(
        &self,
        fs: &dyn Fs,
    ) -> Result<Vec<RecentWorkspace>> {
        let remote_connections = self.remote_connections()?;
        let mut result = Vec::new();
        for (id, paths, identity_paths_hint, remote_connection_id, _session_id, timestamp) in
            self.recent_workspaces()?
        {
            if let Some(remote_connection_id) = remote_connection_id {
                if let Some(connection_options) = remote_connections.get(&remote_connection_id) {
                    result.push(RecentWorkspace {
                        workspace_id: id,
                        location: SerializedWorkspaceLocation::Remote(connection_options.clone()),
                        paths: paths.clone(),
                        identity_paths: identity_paths_hint.unwrap_or(paths),
                        timestamp,
                    });
                }
                continue;
            }

            if paths.paths().is_empty() || contains_wsl_path(&paths) {
                continue;
            }

            if Self::all_paths_exist(paths.paths(), fs, true).await {
                let identity_paths = resolve_local_workspace_identity(fs, &paths)
                    .await
                    .or(identity_paths_hint)
                    .unwrap_or_else(|| paths.clone());
                result.push(RecentWorkspace {
                    workspace_id: id,
                    location: SerializedWorkspaceLocation::Local,
                    paths,
                    identity_paths,
                    timestamp,
                });
            }
        }

        Ok(result)
    }

    // Returns the recent project workspaces suitable for recent-project UIs.
    // Entries are deduplicated by git worktree identity, but preserve the original
    // serialized paths for reopening.
    pub async fn recent_project_workspaces(&self, fs: &dyn Fs) -> Result<Vec<RecentWorkspace>> {
        Ok(dedupe_recent_workspaces(
            self.recent_project_workspaces_ungrouped(fs).await?,
        ))
    }

    pub async fn delete_recent_workspace_group(
        &self,
        target: &RecentWorkspace,
    ) -> Result<Vec<WorkspaceId>> {
        let target_paths = &target.identity_paths;
        let target_remote_connection = match &target.location {
            SerializedWorkspaceLocation::Local => None,
            SerializedWorkspaceLocation::Remote(connection) => {
                Some(remote_connection_identity(connection))
            }
        };

        let remote_connections = self.remote_connections()?;

        let mut workspace_ids = Vec::new();
        for (workspace_id, paths, identity_paths, remote_connection_id, _, _) in
            self.recent_workspaces()?
        {
            let remote_connection = if let Some(id) = remote_connection_id {
                let Some(connection_options) = remote_connections.get(&id) else {
                    continue;
                };
                Some(remote_connection_identity(connection_options))
            } else {
                None
            };
            if remote_connection == target_remote_connection
                && &identity_paths.unwrap_or(paths) == target_paths
            {
                workspace_ids.push(workspace_id);
            }
        }

        self.write(move |connection| {
            connection.with_savepoint("remove_recent_workspace_group", || {
                let mut remove = connection.exec_bound(sql!(
                    UPDATE workspaces SET in_recent_history = FALSE WHERE workspace_id = ?
                ))?;
                for workspace_id in &workspace_ids {
                    remove(*workspace_id)?;
                }
                Ok(workspace_ids)
            })
        })
        .await
    }

    pub async fn garbage_collect_workspaces(
        &self,
        fs: &dyn Fs,
        current_session_id: &str,
        last_session_id: Option<&str>,
    ) -> Result<()> {
        let current_session_id = current_session_id.to_owned();
        let last_session_id = last_session_id.map(str::to_owned);
        self.write({
            let current_session_id = current_session_id.clone();
            let last_session_id = last_session_id.clone();
            move |connection| {
                connection.exec_bound(sql!(
                    DELETE FROM workspaces WHERE NOT in_recent_history
                        AND session_id IS NOT ?1 AND (?2 IS NULL OR session_id IS NOT ?2)
                ))?((current_session_id, last_session_id))
            }
        })
        .await?;
        let remote_connections = self.remote_connections()?;
        let now = Utc::now();
        let mut workspaces_to_delete = Vec::new();
        for (id, paths, _identity_paths_hint, remote_connection_id, session_id, timestamp) in
            self.recent_workspaces()?
        {
            if let Some(session_id) = session_id.as_deref() {
                if session_id == current_session_id
                    || Some(session_id) == last_session_id.as_deref()
                {
                    continue;
                }
            }

            if let Some(remote_connection_id) = remote_connection_id {
                if !remote_connections.contains_key(&remote_connection_id) {
                    workspaces_to_delete.push(id);
                }
                continue;
            }

            // Delete the workspace if any of the paths are WSL paths. If a
            // local workspace points to WSL, attempting to read its metadata
            // will wait for the WSL VM and file server to boot up. This can
            // block for many seconds. Supported scenarios use remote
            // workspaces.
            if contains_wsl_path(&paths) {
                workspaces_to_delete.push(id);
                continue;
            }

            if !Self::all_paths_exist(paths.paths(), fs, true).await
                && now - timestamp >= chrono::Duration::days(7)
            {
                workspaces_to_delete.push(id);
            }
        }

        futures::future::try_join_all(
            workspaces_to_delete
                .into_iter()
                .map(|id| self.delete_workspace_by_id(id)),
        )
        .await?;
        Ok(())
    }

    pub async fn last_workspace(&self, fs: &dyn Fs) -> Result<Option<RecentWorkspace>> {
        Ok(self.recent_project_workspaces(fs).await?.into_iter().next())
    }

    // Returns the locations of the workspaces that were still opened when the last
    // session was closed (i.e. when Zed was quit).
    // If `last_session_window_order` is provided, the returned locations are ordered
    // according to that.
    pub async fn last_session_workspace_locations(
        &self,
        last_session_id: &str,
        last_session_window_stack: Option<Vec<WindowId>>,
        fs: &dyn Fs,
    ) -> Result<Vec<SessionWorkspace>> {
        let mut workspaces = Vec::new();

        for (workspace_id, paths, window_id, remote_connection_id) in
            self.session_workspaces(last_session_id.to_owned())?
        {
            let window_id = window_id.map(WindowId::from);

            if let Some(remote_connection_id) = remote_connection_id {
                workspaces.push(SessionWorkspace {
                    workspace_id,
                    location: SerializedWorkspaceLocation::Remote(
                        self.remote_connection(remote_connection_id)?,
                    ),
                    paths,
                    window_id,
                });
                continue;
            }

            if Self::all_paths_exist(paths.paths(), fs, false).await
                || self.select_row_bound::<_, ItemId>(sql!(
                    SELECT item_id FROM items WHERE workspace_id = ? LIMIT 1
                ))?(workspace_id)?
                .is_some()
            {
                workspaces.push(SessionWorkspace {
                    workspace_id,
                    location: SerializedWorkspaceLocation::Local,
                    paths,
                    window_id,
                });
            }
        }

        if let Some(stack) = last_session_window_stack {
            workspaces.sort_by_key(|workspace| {
                workspace
                    .window_id
                    .and_then(|id| stack.iter().position(|&order_id| order_id == id))
                    .unwrap_or(usize::MAX)
            });
        }

        Ok(workspaces)
    }

    fn get_center_pane_group(&self, workspace_id: WorkspaceId) -> Result<SerializedPaneGroup> {
        Ok(self
            .get_pane_group(workspace_id, None)?
            .into_iter()
            .next()
            .unwrap_or_else(|| {
                SerializedPaneGroup::Pane(SerializedPane {
                    active: true,
                    children: vec![],
                    pinned_count: 0,
                })
            }))
    }

    fn get_pane_group(
        &self,
        workspace_id: WorkspaceId,
        group_id: Option<GroupId>,
    ) -> Result<Vec<SerializedPaneGroup>> {
        type GroupKey = (Option<GroupId>, WorkspaceId);
        type GroupOrPane = (
            Option<GroupId>,
            Option<SerializedAxis>,
            Option<PaneId>,
            Option<bool>,
            Option<usize>,
            Option<String>,
        );
        self.select_bound::<GroupKey, GroupOrPane>(sql!(
            SELECT group_id, axis, pane_id, active, pinned_count, flexes
                FROM (SELECT
                        group_id,
                        axis,
                        NULL as pane_id,
                        NULL as active,
                        NULL as pinned_count,
                        position,
                        parent_group_id,
                        workspace_id,
                        flexes
                      FROM pane_groups
                    UNION
                      SELECT
                        NULL,
                        NULL,
                        center_panes.pane_id,
                        panes.active as active,
                        pinned_count,
                        position,
                        parent_group_id,
                        panes.workspace_id as workspace_id,
                        NULL
                      FROM center_panes
                      JOIN panes ON center_panes.pane_id = panes.pane_id)
                WHERE parent_group_id IS ? AND workspace_id = ?
                ORDER BY position
        ))?((group_id, workspace_id))?
        .into_iter()
        .map(|(group_id, axis, pane_id, active, pinned_count, flexes)| {
            let maybe_pane = maybe!({ Some((pane_id?, active?, pinned_count?)) });
            if let Some((group_id, axis)) = group_id.zip(axis) {
                let flexes = flexes
                    .map(|flexes: String| serde_json::from_str::<Vec<f32>>(&flexes))
                    .transpose()?;

                Ok(SerializedPaneGroup::Group {
                    axis,
                    children: self.get_pane_group(workspace_id, Some(group_id))?,
                    flexes,
                })
            } else if let Some((pane_id, active, pinned_count)) = maybe_pane {
                Ok(SerializedPaneGroup::Pane(SerializedPane::new(
                    self.get_items(pane_id)?,
                    active,
                    pinned_count,
                )))
            } else {
                bail!("Pane Group Child was neither a pane group or a pane");
            }
        })
        // Filter out panes and pane groups which don't have any children or items
        .filter(|pane_group| match pane_group {
            Ok(SerializedPaneGroup::Group { children, .. }) => !children.is_empty(),
            Ok(SerializedPaneGroup::Pane(pane)) => !pane.children.is_empty(),
            _ => true,
        })
        .collect::<Result<_>>()
    }

    fn save_pane_group(
        conn: &Connection,
        workspace_id: WorkspaceId,
        pane_group: &SerializedPaneGroup,
        parent: Option<(GroupId, usize)>,
    ) -> Result<()> {
        if parent.is_none() {
            log::debug!("Saving a pane group for workspace {workspace_id:?}");
        }
        match pane_group {
            SerializedPaneGroup::Group {
                axis,
                children,
                flexes,
            } => {
                let (parent_id, position) = parent.unzip();

                let flex_string = flexes
                    .as_ref()
                    .map(|flexes| serde_json::json!(flexes).to_string());

                let group_id = conn.select_row_bound::<_, i64>(sql!(
                    INSERT INTO pane_groups(
                        workspace_id,
                        parent_group_id,
                        position,
                        axis,
                        flexes
                    )
                    VALUES (?, ?, ?, ?, ?)
                    RETURNING group_id
                ))?((
                    workspace_id,
                    parent_id,
                    position,
                    *axis,
                    flex_string,
                ))?
                .context("Couldn't retrieve group_id from inserted pane_group")?;

                for (position, group) in children.iter().enumerate() {
                    Self::save_pane_group(conn, workspace_id, group, Some((group_id, position)))?
                }

                Ok(())
            }
            SerializedPaneGroup::Pane(pane) => {
                Self::save_pane(conn, workspace_id, pane, parent)?;
                Ok(())
            }
        }
    }

    fn save_pane(
        conn: &Connection,
        workspace_id: WorkspaceId,
        pane: &SerializedPane,
        parent: Option<(GroupId, usize)>,
    ) -> Result<PaneId> {
        let pane_id = conn.select_row_bound::<_, i64>(sql!(
            INSERT INTO panes(workspace_id, active, pinned_count)
            VALUES (?, ?, ?)
            RETURNING pane_id
        ))?((workspace_id, pane.active, pane.pinned_count))?
        .context("Could not retrieve inserted pane_id")?;

        let (parent_id, order) = parent.unzip();
        conn.exec_bound(sql!(
            INSERT INTO center_panes(pane_id, parent_group_id, position)
            VALUES (?, ?, ?)
        ))?((pane_id, parent_id, order))?;

        Self::save_items(conn, workspace_id, pane_id, &pane.children).context("Saving items")?;

        Ok(pane_id)
    }

    fn get_items(&self, pane_id: PaneId) -> Result<Vec<SerializedItem>> {
        self.select_bound(sql!(
            SELECT kind, item_id, active, preview FROM items
            WHERE pane_id = ?
                ORDER BY position
        ))?(pane_id)
    }

    fn save_items(
        conn: &Connection,
        workspace_id: WorkspaceId,
        pane_id: PaneId,
        items: &[SerializedItem],
    ) -> Result<()> {
        let mut insert = conn.exec_bound(sql!(
            INSERT INTO items(workspace_id, pane_id, position, kind, item_id, active, preview) VALUES (?, ?, ?, ?, ?, ?, ?)
        )).context("Preparing insertion")?;
        for (position, item) in items.iter().enumerate() {
            insert((workspace_id, pane_id, position, item))?;
        }

        Ok(())
    }

    query! {
        pub async fn update_timestamp(workspace_id: WorkspaceId) -> Result<()> {
            UPDATE workspaces
            SET timestamp = CURRENT_TIMESTAMP
            WHERE workspace_id = ?
        }
    }

    #[cfg(test)]
    query! {
        pub(crate) async fn set_timestamp_for_tests(workspace_id: WorkspaceId, timestamp: String) -> Result<()> {
            UPDATE workspaces
            SET timestamp = ?2
            WHERE workspace_id = ?1
        }
    }

    query! {
        pub(crate) async fn set_window_open_status(workspace_id: WorkspaceId, bounds: SerializedWindowBounds, display: Uuid, native_window_state: Option<Vec<u8>>) -> Result<()> {
            UPDATE workspaces
            SET window_state = ?2,
                window_x = ?3,
                window_y = ?4,
                window_width = ?5,
                window_height = ?6,
                display = ?7,
                native_window_state = ?8
            WHERE workspace_id = ?1
        }
    }

    query! {
        pub(crate) fn native_window_state(workspace_id: WorkspaceId) -> Result<Option<(Option<Uuid>, Option<Vec<u8>>)>> {
            SELECT display, native_window_state
            FROM workspaces
            WHERE workspace_id = ?
        }
    }

    query! {
        pub(crate) async fn set_centered_layout(workspace_id: WorkspaceId, centered_layout: bool) -> Result<()> {
            UPDATE workspaces
            SET centered_layout = ?2
            WHERE workspace_id = ?1
        }
    }

    #[cfg(any(test, feature = "test-support"))]
    pub async fn adopt_session_workspaces_for_test(
        &self,
        workspace_ids: Vec<WorkspaceId>,
        session_id: String,
    ) -> Result<()> {
        let workspaces = workspace_ids
            .into_iter()
            .map(|workspace_id| {
                let workspace = self
                    .workspace_for_id(workspace_id)
                    .context("Missing workspace")?;
                Ok(SessionWorkspace {
                    workspace_id,
                    location: workspace.location,
                    paths: workspace.paths,
                    window_id: workspace.window_id.map(WindowId::from),
                })
            })
            .collect::<Result<Vec<_>>>()?;
        self.adopt_session_workspaces(&workspaces, session_id).await
    }

    pub async fn adopt_session_workspaces(
        &self,
        workspaces: &[SessionWorkspace],
        session_id: String,
    ) -> Result<()> {
        let workspaces = workspaces
            .iter()
            .map(|workspace| (workspace.workspace_id, workspace.window_id))
            .collect::<Vec<_>>();
        self.write(move |connection| {
            connection.with_savepoint("adopt_session_workspaces", || {
                let mut windows = HashMap::default();
                let default_state = serde_json::to_string(&model::MultiWorkspaceState::default())?;
                for (workspace_id, window_id) in workspaces {
                    let Some((restoring_id, previous_session)) = connection
                        .select_row_bound::<_, (Option<i64>, Option<String>)>(sql!(
                            SELECT restoring_window_id, session_id
                            FROM workspaces WHERE workspace_id = ?
                        ))?(workspace_id)? else { continue };
                    let restoring_id = if let Some(id) = restoring_id.filter(|_| window_id.is_some()) {
                        id
                    } else {
                        let key = window_id.map(|id| (previous_session, id));
                        if let Some(id) = key.as_ref().and_then(|key| windows.get(key)) {
                            *id
                        } else {
                            let state = if let Some(window_id) = window_id {
                                connection.select_row_bound::<_, String>(sql!(
                                    SELECT value FROM scoped_kv_store
                                    WHERE namespace = ?1 AND key = ?2
                                ))?(("multi_workspace_state", window_id.as_u64().to_string()))?
                            } else {
                                None
                            }.unwrap_or_else(|| default_state.clone());
                            let id = connection.select_row_bound::<_, i64>(sql!(
                                INSERT INTO restoring_windows(state) VALUES (?) RETURNING id
                            ))?(state)?.context("creating restored window group")?;
                            if let Some(key) = key {
                                windows.insert(key, id);
                            }
                            id
                        }
                    };
                    connection.exec_bound(sql!(
                        UPDATE workspaces SET session_id = ?2, restoring_window_id = ?3
                        WHERE workspace_id = ?1
                    ))?((workspace_id, session_id.as_str(), restoring_id))?;
                }
                connection.exec(sql!(
                    DELETE FROM restoring_windows WHERE id NOT IN (
                        SELECT restoring_window_id FROM workspaces WHERE restoring_window_id IS NOT NULL
                    )
                ))?()?;
                Ok(())
            })
        })
        .await
    }

    pub(crate) async fn save_multi_workspace(
        &self,
        window_id: WindowId,
        restoring_window_id: Option<i64>,
        session_id: Option<String>,
        workspace_ids: Vec<WorkspaceId>,
        state: model::MultiWorkspaceState,
    ) -> Result<()> {
        self.write(move |connection| {
            connection.with_savepoint("save_multi_workspace", || {
                connection.exec_bound(sql!(
                    INSERT OR REPLACE INTO scoped_kv_store(namespace, key, value)
                    VALUES (?1, ?2, ?3)
                ))?((
                    "multi_workspace_state",
                    window_id.as_u64().to_string(),
                    serde_json::to_string(&state)?,
                ))?;
                let Some((restoring_window_id, session_id)) = restoring_window_id.zip(session_id)
                else {
                    return Ok(());
                };
                let Some(saved_state) =
                    connection.select_row_bound::<_, String>(sql!(
                        SELECT state FROM restoring_windows WHERE id = ?1 AND EXISTS (
                            SELECT workspace_id FROM workspaces
                            WHERE restoring_window_id = ?1 AND session_id = ?2
                        )
                    ))?((restoring_window_id, session_id.as_str()))?
                else {
                    return Ok(());
                };
                let mut saved_state =
                    serde_json::from_str::<model::MultiWorkspaceState>(&saved_state)?;
                let pending_rootless_remote = if let Some(workspace_id) =
                    saved_state.active_workspace_id
                    && !workspace_ids.contains(&workspace_id)
                {
                    connection.select_row_bound::<_, WorkspaceId>(sql!(
                        SELECT workspace_id FROM workspaces
                        WHERE workspace_id = ?1 AND restoring_window_id = ?2 AND session_id = ?3
                            AND remote_connection_id IS NOT NULL AND coalesce(paths, "") = ""
                    ))?((
                        workspace_id,
                        restoring_window_id,
                        session_id.as_str(),
                    ))?
                    .is_some()
                } else {
                    false
                };
                if !pending_rootless_remote {
                    saved_state.active_workspace_id = state
                        .active_workspace_id
                        .or(saved_state.active_workspace_id);
                }
                saved_state.project_groups = state.project_groups;
                for workspace_id in workspace_ids {
                    connection.exec_bound(sql!(
                        UPDATE workspaces SET restoring_window_id = ?2
                        WHERE workspace_id = ?1 AND session_id = ?3 AND window_id = ?4
                            AND (restoring_window_id IS NULL OR restoring_window_id = ?2)
                    ))?((
                        workspace_id,
                        restoring_window_id,
                        session_id.as_str(),
                        window_id.as_u64(),
                    ))?;
                }
                connection.exec_bound(sql!(
                    UPDATE restoring_windows SET state = ?2 WHERE id = ?1
                ))?((restoring_window_id, serde_json::to_string(&saved_state)?))?;
                Ok(())
            })
        })
        .await
    }

    pub(crate) async fn complete_window_restoration(
        &self,
        restoring_window_id: i64,
        session_id: String,
        window_id: WindowId,
        state: model::MultiWorkspaceState,
    ) -> Result<()> {
        let state = serde_json::to_string(&state)?;
        self.write(move |connection| {
            connection.with_savepoint("complete_window_restoration", || {
                if connection.select_row_bound::<_, WorkspaceId>(sql!(
                    SELECT workspace_id FROM workspaces
                    WHERE restoring_window_id = ?1 AND session_id = ?2 LIMIT 1
                ))?((restoring_window_id, session_id.as_str()))?.is_none() {
                    return Ok(());
                }
                connection.exec_bound(sql!(
                    INSERT OR REPLACE INTO scoped_kv_store(namespace, key, value)
                    VALUES (?1, ?2, ?3)
                ))?(("multi_workspace_state", window_id.as_u64().to_string(), state))?;
                connection.exec_bound(sql!(
                    UPDATE workspaces SET window_id = ?2, restoring_window_id = NULL
                    WHERE restoring_window_id = ?1 AND session_id = ?3
                ))?((restoring_window_id, window_id.as_u64(), session_id))?;
                connection.exec(sql!(
                    DELETE FROM restoring_windows WHERE id NOT IN (
                        SELECT restoring_window_id FROM workspaces WHERE restoring_window_id IS NOT NULL
                    )
                ))?()?;
                Ok(())
            })
        })
        .await
    }

    query! {
        pub(crate) fn restoring_window(workspace_id: WorkspaceId) -> Result<Option<(i64, String)>> {
            SELECT restoring_windows.id, restoring_windows.state
            FROM workspaces JOIN restoring_windows ON restoring_window_id = restoring_windows.id
            WHERE workspace_id = ?
        }
    }

    query! {
        pub(crate) fn local_workspace_is_in_window(workspace_id: WorkspaceId, session_id: String, window_id: u64) -> Result<bool> {
            SELECT EXISTS (
                SELECT workspace_id FROM workspaces
                WHERE workspace_id = ?1 AND session_id = ?2 AND window_id = ?3
                    AND remote_connection_id IS NULL AND restoring_window_id IS NULL
            )
        }
    }

    query! {
        pub(crate) fn restoring_window_id(workspace_id: WorkspaceId, session_id: String) -> Result<Option<i64>> {
            SELECT restoring_window_id FROM workspaces
            WHERE workspace_id = ?1 AND session_id = ?2 AND restoring_window_id IS NOT NULL
        }
    }

    query! {
        pub(crate) fn window_workspace_bindings(session_id: String, window_id: u64, restoring_window_id: Option<i64>) -> Result<Vec<(WorkspaceId, WorkspaceBinding)>> {
            SELECT workspace_id, session_id, window_id, restoring_window_id
            FROM workspaces
            WHERE session_id = ?1 AND (
                (restoring_window_id IS NULL AND window_id = ?2) OR restoring_window_id = ?3
            )
            ORDER BY workspace_id
        }
    }

    pub(crate) async fn remove_workspaces_from_session(
        &self,
        workspaces: Vec<(WorkspaceId, WorkspaceBinding)>,
        close_loaded_workspaces: bool,
    ) -> Result<()> {
        self.write(move |connection| {
            connection.with_savepoint("remove_workspaces_from_session", || {
                let mut remove = connection.exec_bound(sql!(
                    UPDATE workspaces
                    SET session_id = NULL, window_id = NULL, restoring_window_id = NULL
                    WHERE workspace_id = ?1 AND session_id IS ?2 AND window_id IS ?3
                        AND restoring_window_id IS ?4
                        AND (?5 OR NOT (
                            remote_connection_id IS NULL AND coalesce(paths, "") = "" AND EXISTS (
                                SELECT item_id FROM items WHERE items.workspace_id = workspaces.workspace_id
                            )
                        ))
                ))?;
                for (workspace_id, binding) in workspaces {
                    remove((workspace_id, binding, close_loaded_workspaces))?;
                }
                Ok(())
            })
        })
        .await
    }

    query! {
        pub(crate) fn workspace_binding(workspace_id: WorkspaceId) -> Result<Option<WorkspaceBinding>> {
            SELECT session_id, window_id, restoring_window_id
            FROM workspaces WHERE workspace_id = ?
        }
    }

    pub(crate) async fn claim_workspace(
        &self,
        workspace_id: WorkspaceId,
        expected_binding: WorkspaceBinding,
        binding: WorkspaceBinding,
        source_workspace_id: Option<WorkspaceId>,
    ) -> Result<bool> {
        self.write(move |connection| {
            Ok(connection.select_row_bound::<_, WorkspaceId>(sql!(
                UPDATE workspaces
                SET session_id = ?2, window_id = ?3, restoring_window_id = ?4, in_recent_history = TRUE
                WHERE workspace_id = ?1 AND ?2 IS NOT NULL AND session_id IS ?5 AND window_id IS ?6
                    AND restoring_window_id IS ?7
                    AND (?8 IS NULL OR EXISTS (
                        SELECT source.workspace_id FROM workspaces AS source
                        WHERE source.workspace_id = ?8
                            AND source.session_id IS ?2 AND source.window_id IS ?3
                    ))
                RETURNING workspace_id
            ))?((workspace_id, binding, expected_binding, source_workspace_id))?
            .is_some())
        })
        .await
    }

    #[cfg(any(test, feature = "test-support"))]
    query! {
        pub(crate) async fn set_session_binding(workspace_id: WorkspaceId, session_id: Option<String>, window_id: Option<u64>) -> Result<()> {
            UPDATE workspaces
            SET restoring_window_id = CASE WHEN session_id IS ?2 THEN restoring_window_id END,
                session_id = ?2, window_id = ?3
            WHERE workspace_id = ?1
        }
    }

    pub(crate) async fn toolchains(
        &self,
        workspace_id: WorkspaceId,
    ) -> Result<Vec<(Toolchain, Arc<Path>, Arc<RelPath>)>> {
        self.write(move |this| {
            let mut select = this
                .select_bound(sql!(
                    SELECT
                        name, path, worktree_root_path, relative_worktree_path, language_name, raw_json
                    FROM toolchains
                    WHERE workspace_id = ?
                ))
                .context("select toolchains")?;

            let toolchain: Vec<(String, String, String, String, String, String)> =
                select(workspace_id)?;

            Ok(toolchain
                .into_iter()
                .filter_map(
                    |(name, path, worktree_root_path, relative_worktree_path, language, json)| {
                        Some((
                            Toolchain {
                                name: name.into(),
                                path: path.into(),
                                language_name: LanguageName::new(&language),
                                as_json: serde_json::Value::from_str(&json).ok()?,
                            },
                           Arc::from(worktree_root_path.as_ref()),
                            RelPath::from_unix_str(&relative_worktree_path).log_err()?.into(),
                        ))
                    },
                )
                .collect())
        })
        .await
    }

    pub async fn set_toolchain(
        &self,
        workspace_id: WorkspaceId,
        worktree_root_path: Arc<Path>,
        relative_worktree_path: Arc<RelPath>,
        toolchain: Toolchain,
    ) -> Result<()> {
        log::debug!(
            "Setting toolchain for workspace, worktree: {worktree_root_path:?}, relative path: {relative_worktree_path:?}, toolchain: {}",
            toolchain.name
        );
        self.write(move |conn| {
            let mut insert = conn
                .exec_bound(sql!(
                    INSERT INTO toolchains(workspace_id, worktree_root_path, relative_worktree_path, language_name, name, path, raw_json) VALUES (?, ?, ?, ?, ?,  ?, ?)
                    ON CONFLICT DO
                    UPDATE SET
                        name = ?5,
                        path = ?6,
                        raw_json = ?7
                ))
                .context("Preparing insertion")?;

            insert((
                workspace_id,
                worktree_root_path.to_string_lossy().into_owned(),
                relative_worktree_path.as_unix_str(),
                toolchain.language_name.as_ref(),
                toolchain.name.as_ref(),
                toolchain.path.as_ref(),
                toolchain.as_json.to_string(),
            ))?;

            Ok(())
        }).await
    }

    pub(crate) async fn save_trusted_worktrees(
        &self,
        trusted_worktrees: HashMap<Option<RemoteHostLocation>, HashSet<PathBuf>>,
    ) -> anyhow::Result<()> {
        use anyhow::Context as _;
        use db::sqlez::statement::Statement;
        use itertools::Itertools as _;

        self.clear_trusted_worktrees()
            .await
            .context("clearing previous trust state")?;

        let trusted_worktrees = trusted_worktrees
            .into_iter()
            .flat_map(|(host, abs_paths)| {
                abs_paths
                    .into_iter()
                    .map(move |abs_path| (Some(abs_path), host.clone()))
            })
            .collect::<Vec<_>>();
        let mut first_worktree;
        let mut last_worktree = 0_usize;
        for (count, placeholders) in std::iter::once("(?, ?, ?)")
            .cycle()
            .take(trusted_worktrees.len())
            .chunks(MAX_QUERY_PLACEHOLDERS / 3)
            .into_iter()
            .map(|chunk| {
                let mut count = 0;
                let placeholders = chunk
                    .inspect(|_| {
                        count += 1;
                    })
                    .join(", ");
                (count, placeholders)
            })
            .collect::<Vec<_>>()
        {
            first_worktree = last_worktree;
            last_worktree = last_worktree + count;
            let query = format!(
                r#"INSERT INTO trusted_worktrees(absolute_path, user_name, host_name)
VALUES {placeholders};"#
            );

            let trusted_worktrees = trusted_worktrees[first_worktree..last_worktree].to_vec();
            self.write(move |conn| {
                let mut statement = Statement::prepare(conn, query)?;
                let mut next_index = 1;
                for (abs_path, host) in trusted_worktrees {
                    let abs_path = abs_path.as_ref().map(|abs_path| abs_path.to_string_lossy());
                    next_index = statement.bind(
                        &abs_path.as_ref().map(|abs_path| abs_path.as_ref()),
                        next_index,
                    )?;
                    next_index = statement.bind(
                        &host
                            .as_ref()
                            .and_then(|host| Some(host.user_name.as_ref()?.as_str())),
                        next_index,
                    )?;
                    next_index = statement.bind(
                        &host.as_ref().map(|host| host.host_identifier.as_str()),
                        next_index,
                    )?;
                }
                statement.exec()
            })
            .await
            .context("inserting new trusted state")?;
        }
        Ok(())
    }

    pub fn fetch_trusted_worktrees(&self) -> Result<DbTrustedPaths> {
        let trusted_worktrees = self.trusted_worktrees()?;
        Ok(trusted_worktrees
            .into_iter()
            .filter_map(|(abs_path, user_name, host_name)| {
                let db_host = match (user_name, host_name) {
                    (None, Some(host_name)) => Some(RemoteHostLocation {
                        user_name: None,
                        host_identifier: SharedString::new(host_name),
                    }),
                    (Some(user_name), Some(host_name)) => Some(RemoteHostLocation {
                        user_name: Some(SharedString::new(user_name)),
                        host_identifier: SharedString::new(host_name),
                    }),
                    _ => None,
                };
                Some((db_host, abs_path?))
            })
            .fold(HashMap::default(), |mut acc, (remote_host, abs_path)| {
                acc.entry(remote_host)
                    .or_insert_with(HashSet::default)
                    .insert(abs_path);
                acc
            }))
    }

    query! {
        fn trusted_worktrees() -> Result<Vec<(Option<PathBuf>, Option<String>, Option<String>)>> {
            SELECT absolute_path, user_name, host_name
            FROM trusted_worktrees
        }
    }

    query! {
        pub async fn clear_trusted_worktrees() -> Result<()> {
            DELETE FROM trusted_worktrees
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct RecentWorkspace {
    pub workspace_id: WorkspaceId,
    pub location: SerializedWorkspaceLocation,
    pub paths: PathList,
    pub identity_paths: PathList,
    pub timestamp: DateTime<Utc>,
}

impl RecentWorkspace {
    pub fn project_group_key(&self) -> ProjectGroupKey {
        let host = match &self.location {
            SerializedWorkspaceLocation::Local => None,
            SerializedWorkspaceLocation::Remote(options) => Some(options.clone()),
        };
        ProjectGroupKey::new(host, self.identity_paths.clone())
    }
}

async fn resolve_local_workspace_identity(fs: &dyn Fs, paths: &PathList) -> Option<PathList> {
    let raw_paths = paths.paths();
    let resolved_paths = futures::future::join_all(
        raw_paths
            .iter()
            .map(|path| project::git_store::resolve_git_worktree_to_main_repo(fs, path)),
    )
    .await;

    if resolved_paths.iter().all(|resolved| resolved.is_none()) {
        return None;
    }

    let resolved_paths: Vec<PathBuf> = raw_paths
        .iter()
        .zip(resolved_paths.iter())
        .map(|(original, resolved)| {
            resolved
                .as_ref()
                .cloned()
                .unwrap_or_else(|| original.clone())
        })
        .collect();
    let resolved_path_refs: Vec<&Path> = resolved_paths.iter().map(PathBuf::as_path).collect();
    Some(PathList::new(&resolved_path_refs))
}

fn dedupe_recent_workspaces(
    workspaces: impl IntoIterator<Item = RecentWorkspace>,
) -> Vec<RecentWorkspace> {
    let mut indices_by_key: HashMap<(Option<RemoteConnectionIdentity>, Vec<PathBuf>), usize> =
        HashMap::default();
    let mut result: Vec<RecentWorkspace> = Vec::new();
    for workspace in workspaces {
        let location_identity = match &workspace.location {
            SerializedWorkspaceLocation::Local => None,
            SerializedWorkspaceLocation::Remote(connection) => {
                Some(remote_connection_identity(connection))
            }
        };
        let key = (location_identity, workspace.identity_paths.paths().to_vec());
        if let Some(&existing_index) = indices_by_key.get(&key) {
            if workspace.timestamp > result[existing_index].timestamp {
                result[existing_index] = workspace;
            }
        } else {
            indices_by_key.insert(key, result.len());
            result.push(workspace);
        }
    }

    result
}

pub fn delete_unloaded_items(
    alive_items: Vec<ItemId>,
    workspace_id: WorkspaceId,
    table: &'static str,
    db: &ThreadSafeConnection,
    cx: &mut App,
) -> Task<Result<()>> {
    let db = db.clone();
    cx.spawn(async move |_| {
        let placeholders = alive_items
            .iter()
            .map(|_| "?")
            .collect::<Vec<&str>>()
            .join(", ");

        let query = format!(
            "DELETE FROM {table} WHERE workspace_id = ? AND item_id NOT IN ({placeholders})"
        );

        db.write(move |conn| {
            let mut statement = Statement::prepare(conn, query)?;
            let mut next_index = statement.bind(&workspace_id, 1)?;
            for id in alive_items {
                next_index = statement.bind(&id, next_index)?;
            }
            statement.exec()
        })
        .await
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PathList;
    use crate::ProjectGroupKey;
    use crate::RemovalIntent;
    use crate::{
        SerializableItemRegistry,
        item::{ItemEvent, SavedItemRestoreError, test::TestItem},
    };
    use crate::{
        multi_workspace::MultiWorkspace,
        persistence::{
            model::{
                SerializedItem, SerializedPane, SerializedPaneGroup, SerializedWorkspace,
                SessionWorkspace,
            },
            read_multi_workspace_state,
        },
    };
    use futures::{FutureExt as _, channel::oneshot, future::Shared};
    use gpui::TaskExt;

    use gpui::{AppContext as _, Global};
    use pretty_assertions::assert_eq;
    use project::Project;
    use remote::SshConnectionOptions;
    use serde_json::json;
    use std::{cell::Cell, io, thread, time::Duration};

    /// Creates a unique directory in a FakeFs, returning the path.
    /// Uses a UUID suffix to avoid collisions with other tests sharing the global DB.
    async fn unique_test_dir(fs: &fs::FakeFs, prefix: &str) -> PathBuf {
        let dir = PathBuf::from(format!("/test-dirs/{}-{}", prefix, uuid::Uuid::new_v4()));
        fs.insert_tree(&dir, json!({})).await;
        dir
    }

    #[gpui::test]
    async fn test_multi_workspace_serializes_on_add_and_remove(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let project1 = Project::test(fs.clone(), [], cx).await;
        let project2 = Project::test(fs.clone(), [], cx).await;

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project1.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| {
            mw.open_sidebar(cx);
        });

        multi_workspace.update_in(cx, |mw, _, cx| {
            mw.set_random_database_id(cx);
        });

        let window_id =
            multi_workspace.update_in(cx, |_, window, _cx| window.window_handle().window_id());

        // --- Add a second workspace ---
        let workspace2 = multi_workspace.update_in(cx, |mw, window, cx| {
            let workspace = cx.new(|cx| crate::Workspace::test_new(project2.clone(), window, cx));
            workspace.update(cx, |ws, _cx| ws.set_random_database_id());
            mw.activate(workspace.clone(), None, window, cx);
            workspace
        });

        // Run background tasks so serialize has a chance to flush.
        cx.run_until_parked();

        // Read back the persisted state and check that the active workspace ID was written.
        let state_after_add = cx.update(|_, cx| read_multi_workspace_state(window_id, cx));
        let active_workspace2_db_id = workspace2.read_with(cx, |ws, _| ws.database_id());
        assert_eq!(
            state_after_add.active_workspace_id, active_workspace2_db_id,
            "After adding a second workspace, the serialized active_workspace_id should match \
             the newly activated workspace's database id"
        );

        // --- Remove the non-active workspace ---
        multi_workspace.update_in(cx, |mw, _window, cx| {
            let active = mw.workspace().clone();
            let ws = mw
                .workspaces()
                .find(|ws| *ws != &active)
                .expect("should have a non-active workspace");
            mw.remove([ws.clone()], RemovalIntent::CloseProject, _window, cx)
                .detach_and_log_err(cx);
        });

        cx.run_until_parked();

        let state_after_remove = cx.update(|_, cx| read_multi_workspace_state(window_id, cx));
        let remaining_db_id =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).database_id());
        assert_eq!(
            state_after_remove.active_workspace_id, remaining_db_id,
            "After removing a workspace, the serialized active_workspace_id should match \
             the remaining active workspace's database id"
        );
    }

    #[gpui::test]
    async fn test_breakpoints() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_breakpoints").await;
        let id = db.next_id().await.unwrap();

        let path = Path::new("/tmp/test.rs");

        let breakpoint = Breakpoint {
            position: 123,
            message: None,
            state: BreakpointState::Enabled,
            condition: None,
            hit_condition: None,
        };

        let log_breakpoint = Breakpoint {
            position: 456,
            message: Some("Test log message".into()),
            state: BreakpointState::Enabled,
            condition: None,
            hit_condition: None,
        };

        let disable_breakpoint = Breakpoint {
            position: 578,
            message: None,
            state: BreakpointState::Disabled,
            condition: None,
            hit_condition: None,
        };

        let condition_breakpoint = Breakpoint {
            position: 789,
            message: None,
            state: BreakpointState::Enabled,
            condition: Some("x > 5".into()),
            hit_condition: None,
        };

        let hit_condition_breakpoint = Breakpoint {
            position: 999,
            message: None,
            state: BreakpointState::Enabled,
            condition: None,
            hit_condition: Some(">= 3".into()),
        };

        let workspace = SerializedWorkspace {
            id,
            paths: PathList::new(&["/tmp"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: {
                let mut map = collections::BTreeMap::default();
                map.insert(
                    Arc::from(path),
                    vec![
                        SourceBreakpoint {
                            row: breakpoint.position,
                            path: Arc::from(path),
                            message: breakpoint.message.clone(),
                            state: breakpoint.state,
                            condition: breakpoint.condition.clone(),
                            hit_condition: breakpoint.hit_condition.clone(),
                        },
                        SourceBreakpoint {
                            row: log_breakpoint.position,
                            path: Arc::from(path),
                            message: log_breakpoint.message.clone(),
                            state: log_breakpoint.state,
                            condition: log_breakpoint.condition.clone(),
                            hit_condition: log_breakpoint.hit_condition.clone(),
                        },
                        SourceBreakpoint {
                            row: disable_breakpoint.position,
                            path: Arc::from(path),
                            message: disable_breakpoint.message.clone(),
                            state: disable_breakpoint.state,
                            condition: disable_breakpoint.condition.clone(),
                            hit_condition: disable_breakpoint.hit_condition.clone(),
                        },
                        SourceBreakpoint {
                            row: condition_breakpoint.position,
                            path: Arc::from(path),
                            message: condition_breakpoint.message.clone(),
                            state: condition_breakpoint.state,
                            condition: condition_breakpoint.condition.clone(),
                            hit_condition: condition_breakpoint.hit_condition.clone(),
                        },
                        SourceBreakpoint {
                            row: hit_condition_breakpoint.position,
                            path: Arc::from(path),
                            message: hit_condition_breakpoint.message.clone(),
                            state: hit_condition_breakpoint.state,
                            condition: hit_condition_breakpoint.condition.clone(),
                            hit_condition: hit_condition_breakpoint.hit_condition.clone(),
                        },
                    ],
                );
                map
            },
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        db.save_workspace(workspace.clone()).await.unwrap();

        let loaded = db.workspace_for_roots(&["/tmp"]).unwrap();
        let loaded_breakpoints = loaded.breakpoints.get(&Arc::from(path)).unwrap();

        assert_eq!(loaded_breakpoints.len(), 5);

        // normal breakpoint
        assert_eq!(loaded_breakpoints[0].row, breakpoint.position);
        assert_eq!(loaded_breakpoints[0].message, breakpoint.message);
        assert_eq!(loaded_breakpoints[0].condition, breakpoint.condition);
        assert_eq!(
            loaded_breakpoints[0].hit_condition,
            breakpoint.hit_condition
        );
        assert_eq!(loaded_breakpoints[0].state, breakpoint.state);
        assert_eq!(loaded_breakpoints[0].path, Arc::from(path));

        // enabled breakpoint
        assert_eq!(loaded_breakpoints[1].row, log_breakpoint.position);
        assert_eq!(loaded_breakpoints[1].message, log_breakpoint.message);
        assert_eq!(loaded_breakpoints[1].condition, log_breakpoint.condition);
        assert_eq!(
            loaded_breakpoints[1].hit_condition,
            log_breakpoint.hit_condition
        );
        assert_eq!(loaded_breakpoints[1].state, log_breakpoint.state);
        assert_eq!(loaded_breakpoints[1].path, Arc::from(path));

        // disable breakpoint
        assert_eq!(loaded_breakpoints[2].row, disable_breakpoint.position);
        assert_eq!(loaded_breakpoints[2].message, disable_breakpoint.message);
        assert_eq!(
            loaded_breakpoints[2].condition,
            disable_breakpoint.condition
        );
        assert_eq!(
            loaded_breakpoints[2].hit_condition,
            disable_breakpoint.hit_condition
        );
        assert_eq!(loaded_breakpoints[2].state, disable_breakpoint.state);
        assert_eq!(loaded_breakpoints[2].path, Arc::from(path));

        // condition breakpoint
        assert_eq!(loaded_breakpoints[3].row, condition_breakpoint.position);
        assert_eq!(loaded_breakpoints[3].message, condition_breakpoint.message);
        assert_eq!(
            loaded_breakpoints[3].condition,
            condition_breakpoint.condition
        );
        assert_eq!(
            loaded_breakpoints[3].hit_condition,
            condition_breakpoint.hit_condition
        );
        assert_eq!(loaded_breakpoints[3].state, condition_breakpoint.state);
        assert_eq!(loaded_breakpoints[3].path, Arc::from(path));

        // hit condition breakpoint
        assert_eq!(loaded_breakpoints[4].row, hit_condition_breakpoint.position);
        assert_eq!(
            loaded_breakpoints[4].message,
            hit_condition_breakpoint.message
        );
        assert_eq!(
            loaded_breakpoints[4].condition,
            hit_condition_breakpoint.condition
        );
        assert_eq!(
            loaded_breakpoints[4].hit_condition,
            hit_condition_breakpoint.hit_condition
        );
        assert_eq!(loaded_breakpoints[4].state, hit_condition_breakpoint.state);
        assert_eq!(loaded_breakpoints[4].path, Arc::from(path));
    }

    #[gpui::test]
    async fn test_remove_last_breakpoint() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_remove_last_breakpoint").await;
        let id = db.next_id().await.unwrap();

        let singular_path = Path::new("/tmp/test_remove_last_breakpoint.rs");

        let breakpoint_to_remove = Breakpoint {
            position: 100,
            message: None,
            state: BreakpointState::Enabled,
            condition: None,
            hit_condition: None,
        };

        let workspace = SerializedWorkspace {
            id,
            paths: PathList::new(&["/tmp"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: {
                let mut map = collections::BTreeMap::default();
                map.insert(
                    Arc::from(singular_path),
                    vec![SourceBreakpoint {
                        row: breakpoint_to_remove.position,
                        path: Arc::from(singular_path),
                        message: None,
                        state: BreakpointState::Enabled,
                        condition: None,
                        hit_condition: None,
                    }],
                );
                map
            },
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        db.save_workspace(workspace.clone()).await.unwrap();

        let loaded = db.workspace_for_roots(&["/tmp"]).unwrap();
        let loaded_breakpoints = loaded.breakpoints.get(&Arc::from(singular_path)).unwrap();

        assert_eq!(loaded_breakpoints.len(), 1);
        assert_eq!(loaded_breakpoints[0].row, breakpoint_to_remove.position);
        assert_eq!(loaded_breakpoints[0].message, breakpoint_to_remove.message);
        assert_eq!(
            loaded_breakpoints[0].condition,
            breakpoint_to_remove.condition
        );
        assert_eq!(
            loaded_breakpoints[0].hit_condition,
            breakpoint_to_remove.hit_condition
        );
        assert_eq!(loaded_breakpoints[0].state, breakpoint_to_remove.state);
        assert_eq!(loaded_breakpoints[0].path, Arc::from(singular_path));

        let workspace_without_breakpoint = SerializedWorkspace {
            id,
            paths: PathList::new(&["/tmp"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: collections::BTreeMap::default(),
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        db.save_workspace(workspace_without_breakpoint.clone())
            .await
            .unwrap();

        let loaded_after_remove = db.workspace_for_roots(&["/tmp"]).unwrap();
        let empty_breakpoints = loaded_after_remove
            .breakpoints
            .get(&Arc::from(singular_path));

        assert!(empty_breakpoints.is_none());
    }

    #[gpui::test]
    async fn test_next_id_stability() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_next_id_stability").await;

        db.write(|conn| {
            conn.migrate(
                "test_table",
                &[sql!(
                    CREATE TABLE test_table(
                        text TEXT,
                        workspace_id INTEGER,
                        FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                        ON DELETE CASCADE
                    ) STRICT;
                )],
                &mut |_, _, _| false,
            )
            .unwrap();
        })
        .await;

        let id = db.next_id().await.unwrap();
        // Assert the empty row got inserted
        assert_eq!(
            Some(id),
            db.select_row_bound::<WorkspaceId, WorkspaceId>(sql!(
                SELECT workspace_id FROM workspaces WHERE workspace_id = ?
            ))
            .unwrap()(id)
            .unwrap()
        );

        db.write(move |conn| {
            conn.exec_bound(sql!(INSERT INTO test_table(text, workspace_id) VALUES (?, ?)))
                .unwrap()(("test-text-1", id))
            .unwrap()
        })
        .await;

        let test_text_1 = db
            .select_row_bound::<_, String>(sql!(SELECT text FROM test_table WHERE workspace_id = ?))
            .unwrap()(1)
        .unwrap()
        .unwrap();
        assert_eq!(test_text_1, "test-text-1");
    }

    #[gpui::test]
    async fn test_native_window_state_round_trip() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_native_window_state_round_trip").await;
        let id = db.next_id().await.unwrap();
        let paths = &["/tmp/native-window-state"];
        let display_uuid = Uuid::new_v4();
        let window_bounds = SerializedWindowBounds(WindowBounds::Windowed(Bounds {
            origin: point(px(100.0), px(200.0)),
            size: size(px(800.0), px(600.0)),
        }));

        db.save_workspace(SerializedWorkspace {
            id,
            paths: PathList::new(paths),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: None,
            display: None,
            docks: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        })
        .await
        .unwrap();
        assert_eq!(db.native_window_state(id).unwrap(), Some((None, None)));
        assert_eq!(
            db.native_window_state(WorkspaceId::from_i64(i64::MAX))
                .unwrap(),
            None
        );

        let state = vec![0u8, 1, 2, 3, 250, 251, 252];
        db.set_window_open_status(id, window_bounds, display_uuid, Some(state.clone()))
            .await
            .unwrap();
        assert_eq!(
            db.native_window_state(id).unwrap(),
            Some((Some(display_uuid), Some(state)))
        );
        let restored = db.workspace_for_roots(paths).unwrap();
        assert_eq!(restored.window_bounds, Some(window_bounds));
        assert_eq!(restored.display, Some(display_uuid));

        let new_state = vec![9u8, 8, 7];
        db.set_window_open_status(id, window_bounds, display_uuid, Some(new_state.clone()))
            .await
            .unwrap();
        assert_eq!(
            db.native_window_state(id).unwrap(),
            Some((Some(display_uuid), Some(new_state)))
        );

        db.set_window_open_status(id, window_bounds, display_uuid, None)
            .await
            .unwrap();
        assert_eq!(
            db.native_window_state(id).unwrap(),
            Some((Some(display_uuid), None))
        );
        assert_eq!(
            db.workspace_for_roots(paths).unwrap().window_bounds,
            Some(window_bounds)
        );
    }

    #[gpui::test]
    async fn test_open_workspace_preserves_native_window_state(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);
        let app_state = cx.update(crate::AppState::test);
        cx.update(|cx| crate::init(app_state.clone(), cx));
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let workspace_id = db.next_id().await.unwrap();
        db.save_workspace(SerializedWorkspace {
            id: workspace_id,
            ..workspace_with(1, &[], empty_pane_group(), None)
        })
        .await
        .unwrap();
        let display = Uuid::new_v4();
        let bounds = SerializedWindowBounds(WindowBounds::Windowed(Bounds {
            origin: point(px(100.0), px(200.0)),
            size: size(px(800.0), px(600.0)),
        }));
        let native_state = vec![0, 1, 2, 255];
        db.set_window_open_status(workspace_id, bounds, display, Some(native_state.clone()))
            .await
            .unwrap();

        cx.update(|cx| crate::open_workspace_by_id(workspace_id, app_state, None, cx))
            .await
            .unwrap();

        assert_eq!(
            db.native_window_state(workspace_id).unwrap(),
            Some((Some(display), Some(native_state)))
        );
        assert_eq!(
            db.workspace_for_id(workspace_id).unwrap().window_bounds,
            Some(bounds)
        );
    }

    #[gpui::test]
    async fn test_workspace_id_stability() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_workspace_id_stability").await;

        db.write(|conn| {
            conn.migrate(
                "test_table",
                &[sql!(
                        CREATE TABLE test_table(
                            text TEXT,
                            workspace_id INTEGER,
                            FOREIGN KEY(workspace_id)
                                REFERENCES workspaces(workspace_id)
                            ON DELETE CASCADE
                        ) STRICT;)],
                &mut |_, _, _| false,
            )
        })
        .await
        .unwrap();

        let mut workspace_1 = SerializedWorkspace {
            id: WorkspaceId(1),
            paths: PathList::new(&["/tmp", "/tmp2"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        let workspace_2 = SerializedWorkspace {
            id: WorkspaceId(2),
            paths: PathList::new(&["/tmp"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        db.save_workspace(workspace_1.clone()).await.unwrap();

        db.write(|conn| {
            conn.exec_bound(sql!(INSERT INTO test_table(text, workspace_id) VALUES (?, ?)))
                .unwrap()(("test-text-1", 1))
            .unwrap();
        })
        .await;

        db.save_workspace(workspace_2.clone()).await.unwrap();

        db.write(|conn| {
            conn.exec_bound(sql!(INSERT INTO test_table(text, workspace_id) VALUES (?, ?)))
                .unwrap()(("test-text-2", 2))
            .unwrap();
        })
        .await;

        workspace_1.paths = PathList::new(&["/tmp", "/tmp3"]);
        db.save_workspace(workspace_1.clone()).await.unwrap();
        db.save_workspace(workspace_1).await.unwrap();
        db.save_workspace(workspace_2).await.unwrap();

        let test_text_2 = db
            .select_row_bound::<_, String>(sql!(SELECT text FROM test_table WHERE workspace_id = ?))
            .unwrap()(2)
        .unwrap()
        .unwrap();
        assert_eq!(test_text_2, "test-text-2");

        let test_text_1 = db
            .select_row_bound::<_, String>(sql!(SELECT text FROM test_table WHERE workspace_id = ?))
            .unwrap()(1)
        .unwrap()
        .unwrap();
        assert_eq!(test_text_1, "test-text-1");
    }

    fn group(axis: Axis, children: Vec<SerializedPaneGroup>) -> SerializedPaneGroup {
        SerializedPaneGroup::Group {
            axis: SerializedAxis(axis),
            flexes: None,
            children,
        }
    }

    #[gpui::test]
    async fn test_full_workspace_serialization() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_full_workspace_serialization").await;

        //  -----------------
        //  | 1,2   | 5,6   |
        //  | - - - |       |
        //  | 3,4   |       |
        //  -----------------
        let center_group = group(
            Axis::Horizontal,
            vec![
                group(
                    Axis::Vertical,
                    vec![
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 5, false, false),
                                SerializedItem::new("Terminal", 6, true, false),
                            ],
                            false,
                            0,
                        )),
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 7, true, false),
                                SerializedItem::new("Terminal", 8, false, false),
                            ],
                            false,
                            0,
                        )),
                    ],
                ),
                SerializedPaneGroup::Pane(SerializedPane::new(
                    vec![
                        SerializedItem::new("Terminal", 9, false, false),
                        SerializedItem::new("Terminal", 10, true, false),
                    ],
                    false,
                    0,
                )),
            ],
        );

        let workspace = SerializedWorkspace {
            id: WorkspaceId(5),
            paths: PathList::new(&["/tmp", "/tmp2"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group,
            window_bounds: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: Some(999),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: (0..20)
                .map(|index| PathBuf::from(format!("/tmp2/src/{index}.rs")))
                .collect(),
        };

        db.save_workspace(workspace.clone()).await.unwrap();

        let round_trip_workspace = db.workspace_for_roots(&["/tmp2", "/tmp"]);
        assert_eq!(workspace, round_trip_workspace.unwrap());

        // Test guaranteed duplicate IDs
        db.save_workspace(workspace.clone()).await.unwrap();
        db.save_workspace(workspace.clone()).await.unwrap();

        let round_trip_workspace = db.workspace_for_roots(&["/tmp", "/tmp2"]);
        assert_eq!(workspace, round_trip_workspace.unwrap());

        assert!(db.delete_workspace_by_id(workspace.id).await.is_ok());
        assert!(db.recent_navigation_history(workspace.id).is_empty());
    }

    #[gpui::test]
    async fn test_snapshot_failure_rolls_back_manifest_and_crossed_payloads() {
        let db = WorkspaceDb(
            db::open_test_db::<(KeyValueStore, WorkspaceDb)>(
                "test_snapshot_failure_rolls_back_manifest_and_crossed_payloads",
            )
            .await,
        );
        let kvp = KeyValueStore::from_app_db(&db::AppDatabase(db.0.clone()));
        let workspace_id = WorkspaceId(1);
        let binding = (Some("session".to_owned()), Some(1), None);
        let saved = workspace_with(
            1,
            &[],
            SerializedPaneGroup::Pane(SerializedPane::new(
                vec![
                    SerializedItem::new("TestItem", 1, false, false),
                    SerializedItem::new("TestItem", 2, true, false),
                ],
                true,
                1,
            )),
            Some("session"),
        );
        let replacement = workspace_with(
            1,
            &[],
            group(
                Axis::Horizontal,
                vec![
                    SerializedPaneGroup::Pane(SerializedPane::new(
                        vec![SerializedItem::new("TestItem", 2, true, false)],
                        false,
                        1,
                    )),
                    SerializedPaneGroup::Pane(SerializedPane::new(
                        vec![SerializedItem::new("TestItem", 1, true, true)],
                        true,
                        0,
                    )),
                ],
            ),
            Some("session"),
        );
        db.save_workspace(saved.clone()).await.unwrap();
        for (item_id, contents) in [(1, "first draft\nλ"), (2, "second draft\n🦀")] {
            kvp.write_kvp(format!("{workspace_id:?}/{item_id}"), contents.to_owned())
                .await
                .unwrap();
        }

        let error = db
            .save_snapshot(
                Some((workspace_id, binding.clone())),
                vec![
                    WorkspaceDb::prepare_save_workspace(replacement.clone()),
                    KeyValueStore::prepare_write_kvp(
                        format!("{workspace_id:?}/2"),
                        "first draft\nλ".to_owned(),
                    ),
                    Box::new(move |connection| {
                        assert_eq!(
                            connection.select::<(String, String)>(sql!(
                                SELECT key, value FROM kv_store ORDER BY key
                            ))?()?,
                            vec![
                                (format!("{workspace_id:?}/1"), "first draft\nλ".to_owned()),
                                (format!("{workspace_id:?}/2"), "first draft\nλ".to_owned()),
                            ]
                        );
                        anyhow::bail!("second payload write failed")
                    }),
                ],
            )
            .await
            .unwrap_err();
        assert_eq!(error.to_string(), "second payload write failed");
        assert_eq!(db.workspace_for_id(workspace_id), Some(saved));
        assert_eq!(
            restoration_payloads(&kvp, workspace_id, [1, 2]),
            ["first draft\nλ", "second draft\n🦀"]
        );

        db.save_snapshot(
            Some((workspace_id, binding)),
            vec![
                WorkspaceDb::prepare_save_workspace(replacement.clone()),
                KeyValueStore::prepare_write_kvp(
                    format!("{workspace_id:?}/2"),
                    "first draft\nλ".to_owned(),
                ),
                KeyValueStore::prepare_write_kvp(
                    format!("{workspace_id:?}/1"),
                    "second draft\n🦀".to_owned(),
                ),
            ],
        )
        .await
        .unwrap();
        assert_eq!(db.workspace_for_id(workspace_id), Some(replacement));
        assert_eq!(
            restoration_payloads(&kvp, workspace_id, [1, 2]),
            ["second draft\n🦀", "first draft\nλ"]
        );
    }

    #[gpui::test]
    async fn test_workspace_assignment() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_basic_functionality").await;

        let workspace_1 = SerializedWorkspace {
            id: WorkspaceId(1),
            paths: PathList::new(&["/tmp", "/tmp2"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: Some(1),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        let mut workspace_2 = SerializedWorkspace {
            id: WorkspaceId(2),
            paths: PathList::new(&["/tmp"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: None,
            window_id: Some(2),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        db.save_workspace(workspace_1.clone()).await.unwrap();
        db.save_workspace(workspace_2.clone()).await.unwrap();

        // Test that paths are treated as a set
        assert_eq!(
            db.workspace_for_roots(&["/tmp", "/tmp2"]).unwrap(),
            workspace_1
        );
        assert_eq!(
            db.workspace_for_roots(&["/tmp2", "/tmp"]).unwrap(),
            workspace_1
        );

        // Make sure that other keys work
        assert_eq!(db.workspace_for_roots(&["/tmp"]).unwrap(), workspace_2);
        assert_eq!(db.workspace_for_roots(&["/tmp3", "/tmp2", "/tmp4"]), None);

        // Test 'mutate' case of updating a pre-existing id
        workspace_2.paths = PathList::new(&["/tmp", "/tmp2"]);

        db.save_workspace(workspace_2.clone()).await.unwrap();
        assert_eq!(
            db.workspace_for_roots(&["/tmp", "/tmp2"]).unwrap(),
            workspace_2
        );

        // Test other mechanism for mutating
        let mut workspace_3 = SerializedWorkspace {
            id: WorkspaceId(3),
            paths: PathList::new(&["/tmp2", "/tmp"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: Some(3),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        db.save_workspace(workspace_3.clone()).await.unwrap();
        assert_eq!(
            db.workspace_for_roots(&["/tmp", "/tmp2"]).unwrap(),
            workspace_3
        );

        // Make sure that updating paths differently also works
        workspace_3.paths = PathList::new(&["/tmp3", "/tmp4", "/tmp2"]);
        db.save_workspace(workspace_3.clone()).await.unwrap();
        assert_eq!(db.workspace_for_roots(&["/tmp2", "tmp"]), None);
        assert_eq!(
            db.workspace_for_roots(&["/tmp2", "/tmp3", "/tmp4"])
                .unwrap(),
            workspace_3
        );
    }

    #[gpui::test]
    async fn test_session_workspaces() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_serializing_workspaces_session_id").await;

        let workspace_1 = SerializedWorkspace {
            id: WorkspaceId(1),
            paths: PathList::new(&["/tmp1"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: Some("session-id-1".to_owned()),
            window_id: Some(10),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        let workspace_2 = SerializedWorkspace {
            id: WorkspaceId(2),
            paths: PathList::new(&["/tmp2"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: Some("session-id-1".to_owned()),
            window_id: Some(20),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        let workspace_3 = SerializedWorkspace {
            id: WorkspaceId(3),
            paths: PathList::new(&["/tmp3"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: Some("session-id-2".to_owned()),
            window_id: Some(30),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        let workspace_4 = SerializedWorkspace {
            id: WorkspaceId(4),
            paths: PathList::new(&["/tmp4"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        let connection_id = db
            .get_or_create_remote_connection(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: "my-host".into(),
                port: Some(1234),
                ..Default::default()
            }))
            .await
            .unwrap();

        let workspace_5 = SerializedWorkspace {
            id: WorkspaceId(5),
            paths: PathList::default(),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Remote(
                db.remote_connection(connection_id).unwrap(),
            ),
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            session_id: Some("session-id-2".to_owned()),
            window_id: Some(50),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        let workspace_6 = SerializedWorkspace {
            id: WorkspaceId(6),
            paths: PathList::new(&["/tmp6c", "/tmp6b", "/tmp6a"]),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: Some("session-id-3".to_owned()),
            window_id: Some(60),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        db.save_workspace(workspace_1.clone()).await.unwrap();
        thread::sleep(Duration::from_millis(1000)); // Force timestamps to increment
        db.save_workspace(workspace_2.clone()).await.unwrap();
        db.save_workspace(workspace_3.clone()).await.unwrap();
        thread::sleep(Duration::from_millis(1000)); // Force timestamps to increment
        db.save_workspace(workspace_4.clone()).await.unwrap();
        db.save_workspace(workspace_5.clone()).await.unwrap();
        db.save_workspace(workspace_6.clone()).await.unwrap();

        let locations = db.session_workspaces("session-id-1".to_owned()).unwrap();
        assert_eq!(locations.len(), 2);
        assert_eq!(locations[0].0, WorkspaceId(2));
        assert_eq!(locations[0].1, PathList::new(&["/tmp2"]));
        assert_eq!(locations[0].2, Some(20));
        assert_eq!(locations[1].0, WorkspaceId(1));
        assert_eq!(locations[1].1, PathList::new(&["/tmp1"]));
        assert_eq!(locations[1].2, Some(10));

        let locations = db.session_workspaces("session-id-2".to_owned()).unwrap();
        assert_eq!(locations.len(), 2);
        assert_eq!(locations[0].0, WorkspaceId(5));
        assert_eq!(locations[0].1, PathList::default());
        assert_eq!(locations[0].2, Some(50));
        assert_eq!(locations[0].3, Some(connection_id));
        assert_eq!(locations[1].0, WorkspaceId(3));
        assert_eq!(locations[1].1, PathList::new(&["/tmp3"]));
        assert_eq!(locations[1].2, Some(30));

        let locations = db.session_workspaces("session-id-3".to_owned()).unwrap();
        assert_eq!(locations.len(), 1);
        assert_eq!(locations[0].0, WorkspaceId(6));
        assert_eq!(
            locations[0].1,
            PathList::new(&["/tmp6c", "/tmp6b", "/tmp6a"]),
        );
        assert_eq!(locations[0].2, Some(60));
    }

    fn default_workspace<P: AsRef<Path>>(
        paths: &[P],
        center_group: &SerializedPaneGroup,
    ) -> SerializedWorkspace {
        SerializedWorkspace {
            id: WorkspaceId(4),
            paths: PathList::new(paths),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: center_group.clone(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        }
    }

    #[gpui::test]
    async fn test_last_session_workspace_locations(cx: &mut gpui::TestAppContext) {
        let dir1 = tempfile::TempDir::with_prefix("dir1").unwrap();
        let dir2 = tempfile::TempDir::with_prefix("dir2").unwrap();
        let dir3 = tempfile::TempDir::with_prefix("dir3").unwrap();
        let dir4 = tempfile::TempDir::with_prefix("dir4").unwrap();

        let fs = fs::FakeFs::new(cx.executor());
        fs.insert_tree(dir1.path(), json!({})).await;
        fs.insert_tree(dir2.path(), json!({})).await;
        fs.insert_tree(dir3.path(), json!({})).await;
        fs.insert_tree(dir4.path(), json!({})).await;

        let db =
            WorkspaceDb::open_test_db("test_serializing_workspaces_last_session_workspaces").await;

        let workspaces = [
            (1, vec![dir1.path()], 9),
            (2, vec![dir2.path()], 5),
            (3, vec![dir3.path()], 8),
            (4, vec![dir4.path()], 2),
            (5, vec![dir1.path(), dir2.path(), dir3.path()], 3),
            (6, vec![dir4.path(), dir3.path(), dir2.path()], 4),
        ]
        .into_iter()
        .map(|(id, paths, window_id)| SerializedWorkspace {
            id: WorkspaceId(id),
            paths: PathList::new(paths.as_slice()),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: Some("one-session".to_owned()),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            window_id: Some(window_id),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        })
        .collect::<Vec<_>>();

        for workspace in workspaces.iter() {
            db.save_workspace(workspace.clone()).await.unwrap();
        }

        let stack = Some(Vec::from([
            WindowId::from(2), // Top
            WindowId::from(8),
            WindowId::from(5),
            WindowId::from(9),
            WindowId::from(3),
            WindowId::from(4), // Bottom
        ]));

        let locations = db
            .last_session_workspace_locations("one-session", stack, fs.as_ref())
            .await
            .unwrap();
        assert_eq!(
            locations,
            [
                SessionWorkspace {
                    workspace_id: WorkspaceId(4),
                    location: SerializedWorkspaceLocation::Local,
                    paths: PathList::new(&[dir4.path()]),
                    window_id: Some(WindowId::from(2u64)),
                },
                SessionWorkspace {
                    workspace_id: WorkspaceId(3),
                    location: SerializedWorkspaceLocation::Local,
                    paths: PathList::new(&[dir3.path()]),
                    window_id: Some(WindowId::from(8u64)),
                },
                SessionWorkspace {
                    workspace_id: WorkspaceId(2),
                    location: SerializedWorkspaceLocation::Local,
                    paths: PathList::new(&[dir2.path()]),
                    window_id: Some(WindowId::from(5u64)),
                },
                SessionWorkspace {
                    workspace_id: WorkspaceId(1),
                    location: SerializedWorkspaceLocation::Local,
                    paths: PathList::new(&[dir1.path()]),
                    window_id: Some(WindowId::from(9u64)),
                },
                SessionWorkspace {
                    workspace_id: WorkspaceId(5),
                    location: SerializedWorkspaceLocation::Local,
                    paths: PathList::new(&[dir1.path(), dir2.path(), dir3.path()]),
                    window_id: Some(WindowId::from(3u64)),
                },
                SessionWorkspace {
                    workspace_id: WorkspaceId(6),
                    location: SerializedWorkspaceLocation::Local,
                    paths: PathList::new(&[dir4.path(), dir3.path(), dir2.path()]),
                    window_id: Some(WindowId::from(4u64)),
                },
            ]
        );
    }

    fn pane_with_items(item_ids: &[ItemId]) -> SerializedPaneGroup {
        SerializedPaneGroup::Pane(SerializedPane::new(
            item_ids
                .iter()
                .map(|id| SerializedItem::new("Terminal", *id, true, false))
                .collect(),
            true,
            0,
        ))
    }

    fn empty_pane_group() -> SerializedPaneGroup {
        SerializedPaneGroup::Pane(SerializedPane::default())
    }

    fn workspace_with(
        id: u64,
        paths: &[&Path],
        center_group: SerializedPaneGroup,
        session_id: Option<&str>,
    ) -> SerializedWorkspace {
        SerializedWorkspace {
            id: WorkspaceId(id as i64),
            paths: PathList::new(paths),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group,
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            centered_layout: false,
            session_id: session_id.map(|s| s.to_owned()),
            window_id: Some(id),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        }
    }

    fn remote_workspace_with(id: u64, host: &str, paths: &[&Path]) -> SerializedWorkspace {
        SerializedWorkspace {
            id: WorkspaceId(id as i64),
            paths: PathList::new(paths),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Remote(RemoteConnectionOptions::Ssh(
                SshConnectionOptions {
                    host: host.into(),
                    ..Default::default()
                },
            )),
            center_group: empty_pane_group(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: Some(id),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        }
    }

    async fn local_recent_workspace(
        workspace_id: WorkspaceId,
        paths: PathList,
        timestamp: DateTime<Utc>,
        fs: &dyn Fs,
    ) -> RecentWorkspace {
        let identity_paths = resolve_local_workspace_identity(fs, &paths)
            .await
            .unwrap_or_else(|| paths.clone());
        RecentWorkspace {
            workspace_id,
            location: SerializedWorkspaceLocation::Local,
            paths,
            identity_paths,
            timestamp,
        }
    }

    #[gpui::test]
    async fn test_scratch_only_workspace_restores_from_last_session(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_scratch_only_workspace_restores_from_last_session")
                .await;

        db.save_workspace(workspace_with(1, &[], pane_with_items(&[100]), Some("s1")))
            .await
            .unwrap();

        let sessions = db
            .last_session_workspace_locations("s1", None, fs.as_ref())
            .await
            .unwrap();
        assert_eq!(sessions.len(), 1);
        assert_eq!(sessions[0].workspace_id, WorkspaceId(1));
        assert!(sessions[0].paths.is_empty());

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();
        assert!(
            recents
                .iter()
                .all(|workspace| workspace.workspace_id != WorkspaceId(1)),
            "scratch-only workspace must not appear in the recent-projects UI"
        );
    }

    #[gpui::test]
    async fn test_last_session_restores_file_only_workspaces(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        fs.insert_tree(
            "/session",
            json!({ "one.txt": "one", "two.txt": "two", "project": {} }),
        )
        .await;
        let db = WorkspaceDb::open_test_db("file_only_session").await;
        for (id, paths) in [
            (1, Vec::new()),
            (2, vec![Path::new("/session/one.txt")]),
            (
                3,
                vec![Path::new("/session/one.txt"), Path::new("/session/two.txt")],
            ),
            (4, vec![Path::new("/session/project")]),
            (5, vec![Path::new("/session/missing.txt")]),
        ] {
            db.save_workspace(workspace_with(
                id,
                &paths,
                pane_with_items(&[id]),
                Some("previous"),
            ))
            .await
            .unwrap();
        }
        let mut restored = db
            .last_session_workspace_locations("previous", None, fs.as_ref())
            .await
            .unwrap()
            .into_iter()
            .map(|workspace| workspace.workspace_id)
            .collect::<Vec<_>>();
        restored.sort();
        let recent = db
            .recent_project_workspaces(fs.as_ref())
            .await
            .unwrap()
            .into_iter()
            .map(|workspace| workspace.workspace_id)
            .collect::<Vec<_>>();
        assert_eq!(
            restored,
            vec![
                WorkspaceId(1),
                WorkspaceId(2),
                WorkspaceId(3),
                WorkspaceId(4),
                WorkspaceId(5),
            ]
        );
        assert_eq!(recent, vec![WorkspaceId(4)]);
    }

    #[gpui::test]
    async fn test_restoring_window_groups_survive_runtime_id_reuse(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        db.write(|connection| {
            connection.exec_bound(sql!(
                INSERT INTO sqlite_sequence(name, seq) VALUES (?1, ?2)
            ))?(("restoring_windows", WindowId::from(1u64).as_u64()))
        })
        .await
        .unwrap();
        let kvp = cx.update(|cx| KeyValueStore::global(cx));
        let fs = fs::FakeFs::new(cx.executor());
        for (id, window_id) in [(1, 10), (2, 10), (3, 20), (4, 30)] {
            db.save_workspace(SerializedWorkspace {
                window_id: Some(window_id),
                ..workspace_with(id, &[], pane_with_items(&[id]), Some("previous"))
            })
            .await
            .unwrap();
        }
        let mut states = [
            model::MultiWorkspaceState {
                active_workspace_id: Some(WorkspaceId(2)),
                sidebar_open: true,
                project_groups: vec![model::SerializedProjectGroup::from_group(
                    &ProjectGroupKey::new(None, PathList::new(&["/first"])),
                    false,
                )],
                sidebar_state: Some("first sidebar".to_owned()),
            },
            model::MultiWorkspaceState {
                active_workspace_id: Some(WorkspaceId(3)),
                sidebar_open: false,
                project_groups: vec![model::SerializedProjectGroup::from_group(
                    &ProjectGroupKey::new(None, PathList::new(&["/second"])),
                    true,
                )],
                sidebar_state: Some("second sidebar".to_owned()),
            },
        ];
        for (window_id, state) in [10u64, 20].into_iter().zip(states.iter()) {
            write_multi_workspace_state(&kvp, WindowId::from(window_id), state.clone()).await;
        }
        for (session, completed) in [("current", false), ("next", false), ("next", true)] {
            db.adopt_session_workspaces_for_test(
                vec![WorkspaceId(1), WorkspaceId(2), WorkspaceId(3)],
                session.to_owned(),
            )
            .await
            .unwrap();
            if session == "current" {
                for (id, window_id) in [(1, 10), (2, 10), (3, 20), (4, 30)] {
                    let saved = db.workspace_for_id(WorkspaceId(id)).unwrap();
                    assert_eq!(
                        (saved.session_id.as_deref(), saved.window_id),
                        (
                            Some(if id == 4 { "previous" } else { session }),
                            Some(window_id)
                        )
                    );
                    assert_eq!(saved.center_group, pane_with_items(&[id as ItemId]));
                }
            }
            db.set_session_binding(WorkspaceId(2), Some(session.to_owned()), Some(20))
                .await
                .unwrap();
            write_multi_workspace_state(
                &kvp,
                WindowId::from(20u64),
                model::MultiWorkspaceState {
                    active_workspace_id: Some(WorkspaceId(2)),
                    ..model::MultiWorkspaceState::default()
                },
            )
            .await;
            if completed {
                states[0].sidebar_state = Some("restored first sidebar".to_owned());
                let pending_id =
                    u64::try_from(db.restoring_window(WorkspaceId(3)).unwrap().unwrap().0).unwrap();
                let live_id = WindowId::from(pending_id);
                assert_eq!(live_id.as_u64(), pending_id);
                fs.insert_tree("/new", json!({})).await;
                db.save_workspace(SerializedWorkspace {
                    window_id: Some(live_id.as_u64()),
                    ..workspace_with(
                        4,
                        &[Path::new("/new")],
                        pane_with_items(&[4]),
                        Some(session),
                    )
                })
                .await
                .unwrap();
                states[0].active_workspace_id = Some(WorkspaceId(4));
                states[0]
                    .project_groups
                    .push(model::SerializedProjectGroup::from_group(
                        &ProjectGroupKey::new(None, PathList::new(&["/new"])),
                        true,
                    ));
                db.complete_window_restoration(
                    db.restoring_window(WorkspaceId(2)).unwrap().unwrap().0,
                    session.to_owned(),
                    live_id,
                    states[0].clone(),
                )
                .await
                .unwrap();
            }
            let locations = db
                .last_session_workspace_locations(session, None, fs.as_ref())
                .await
                .unwrap();
            let restored = cx.update(|cx| read_serialized_multi_workspaces(locations, cx));
            assert_eq!(restored.len(), states.len());
            assert_eq!(
                restored
                    .iter()
                    .map(|window| (
                        window.active_workspace.workspace_id,
                        serde_json::to_value(&window.state).unwrap(),
                    ))
                    .collect::<BTreeMap<_, _>>(),
                states
                    .iter()
                    .map(|state| (
                        state.active_workspace_id.unwrap(),
                        serde_json::to_value(state).unwrap(),
                    ))
                    .collect::<BTreeMap<_, _>>(),
            );
        }
        assert_eq!(db.restoring_window(WorkspaceId(1)).unwrap(), None);
        assert_eq!(db.restoring_window(WorkspaceId(2)).unwrap(), None);
        db.adopt_session_workspaces_for_test(
            vec![WorkspaceId(1), WorkspaceId(2)],
            "next".to_owned(),
        )
        .await
        .unwrap();
        let pending_first = db.restoring_window(WorkspaceId(1)).unwrap();
        let pending_second = db.restoring_window(WorkspaceId(3)).unwrap();
        db.set_session_binding(WorkspaceId(2), None, None)
            .await
            .unwrap();
        db.complete_window_restoration(
            pending_first.as_ref().unwrap().0,
            "previous".to_owned(),
            WindowId::from(30u64),
            states[1].clone(),
        )
        .await
        .unwrap();
        assert_eq!(db.restoring_window(WorkspaceId(1)).unwrap(), pending_first);
        assert_eq!(db.restoring_window(WorkspaceId(3)).unwrap(), pending_second);
        let live_id = WindowId::from(
            db.workspace_for_id(WorkspaceId(4))
                .unwrap()
                .window_id
                .unwrap(),
        );
        db.complete_window_restoration(
            pending_first.unwrap().0,
            "next".to_owned(),
            live_id,
            states[0].clone(),
        )
        .await
        .unwrap();
        assert_eq!(db.restoring_window(WorkspaceId(1)).unwrap(), None);
        assert_eq!(db.restoring_window(WorkspaceId(2)).unwrap(), None);
        let detached = db.workspace_for_id(WorkspaceId(2)).unwrap();
        assert_eq!((detached.session_id, detached.window_id), (None, None));
        db.complete_window_restoration(
            pending_second.unwrap().0,
            "next".to_owned(),
            WindowId::from(10u64),
            states[1].clone(),
        )
        .await
        .unwrap();
        assert_eq!(db.restoring_window(WorkspaceId(3)).unwrap(), None);
        assert_eq!(
            db.select_row::<i64>(sql!(SELECT count(*) FROM restoring_windows))
                .unwrap()()
            .unwrap(),
            Some(0)
        );

        let mut source = db.workspace_for_id(WorkspaceId(3)).unwrap();
        source.location = remote_workspace_with(3, "rootless-remote", &[]).location;
        db.save_workspace(source.clone()).await.unwrap();
        db.adopt_session_workspaces_for_test(vec![source.id], "next".to_owned())
            .await
            .unwrap();
        let restoring_id = db.restoring_window(source.id).unwrap().unwrap().0;
        db.set_session_binding(WorkspaceId(2), Some("next".to_owned()), Some(30))
            .await
            .unwrap();
        for loaded in [false, true] {
            let mut workspace_ids = vec![WorkspaceId(2)];
            if loaded {
                db.set_session_binding(source.id, Some("next".to_owned()), Some(30))
                    .await
                    .unwrap();
                workspace_ids.push(source.id);
            }
            db.save_multi_workspace(
                WindowId::from(30u64),
                Some(restoring_id),
                Some("next".to_owned()),
                workspace_ids,
                model::MultiWorkspaceState {
                    active_workspace_id: Some(WorkspaceId(2)),
                    ..states[1].clone()
                },
            )
            .await
            .unwrap();
            let (group_id, state) = db.restoring_window(source.id).unwrap().unwrap();
            let state = serde_json::from_str::<model::MultiWorkspaceState>(&state).unwrap();
            assert_eq!(group_id, restoring_id);
            assert_eq!(
                state.active_workspace_id,
                Some(if loaded { WorkspaceId(2) } else { source.id })
            );
            assert_eq!(
                db.workspace_for_id(source.id).unwrap().center_group,
                source.center_group
            );
        }
    }

    #[gpui::test]
    async fn test_inaccessible_saved_local_root_preserves_workspace(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);
        let app_state = cx.update(crate::AppState::test);
        let fs = app_state.fs.as_fake();
        let root = Path::new(util::path!("/session"));
        fs.insert_tree(root, json!({ "available": {}, "inaccessible": {} }))
            .await;
        let inaccessible = root.join("inaccessible");
        let paths = vec![root.join("available"), inaccessible.clone()];
        fs.set_metadata_error(&inaccessible, io::ErrorKind::PermissionDenied);
        cx.update(|cx| crate::init(app_state.clone(), cx));
        let error = fs.metadata(&inaccessible).await.unwrap_err();
        assert_eq!(
            error.downcast_ref::<io::Error>().unwrap().kind(),
            io::ErrorKind::PermissionDenied
        );
        let session_id = cx.update(|cx| app_state.session.read(cx).id().to_owned());
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let kvp = cx.update(|cx| KeyValueStore::global(cx));
        let workspace_id = db.next_id().await.unwrap();
        let saved = workspace_with(
            workspace_id.0 as u64,
            &paths.iter().map(PathBuf::as_path).collect::<Vec<_>>(),
            SerializedPaneGroup::Pane(SerializedPane::new(
                vec![SerializedItem::new("TestItem", 1, true, false)],
                true,
                0,
            )),
            Some("previous"),
        );
        db.save_workspace(saved.clone()).await.unwrap();
        kvp.write_kvp(format!("{workspace_id:?}/1"), "saved draft".to_owned())
            .await
            .unwrap();
        db.adopt_session_workspaces_for_test(vec![workspace_id], session_id.clone())
            .await
            .unwrap();
        let session = db.session_workspaces(session_id.clone()).unwrap();
        let restoring_group = db.restoring_window(workspace_id).unwrap();

        let result = cx
            .update(|cx| {
                crate::Workspace::new_local(
                    paths,
                    app_state,
                    None,
                    None,
                    None,
                    crate::OpenMode::NewWindow,
                    cx,
                )
            })
            .await;
        assert!(result.is_err());
        assert_eq!(cx.windows().len(), 0);
        let persisted = db.workspace_for_id(workspace_id).unwrap();
        assert_eq!(persisted.paths, saved.paths);
        assert_eq!(persisted.center_group, saved.center_group);
        assert_eq!(db.session_workspaces(session_id).unwrap(), session);
        assert_eq!(db.restoring_window(workspace_id).unwrap(), restoring_group);
        assert_eq!(
            kvp.read_kvp(&format!("{workspace_id:?}/1")).unwrap(),
            Some("saved draft".to_owned())
        );
    }

    #[gpui::test]
    async fn test_failed_dirty_item_restoration_preserves_complete_snapshot(
        cx: &mut gpui::TestAppContext,
    ) {
        struct RestoreFailure {
            fail: bool,
            completed: Vec<ItemId>,
            cleanups: usize,
        }
        impl Global for RestoreFailure {}

        for split in [false, true] {
            let cx = &mut cx.new_app();
            crate::tests::init_test(cx);
            cx.update(|cx| {
                crate::register_serializable_item::<TestItem>(cx);
                cx.set_global(RestoreFailure {
                    fail: true,
                    completed: Vec::new(),
                    cleanups: 0,
                });
            });
            let fs = fs::FakeFs::new(cx.executor());
            let project = Project::test(fs, [], cx).await;
            let (multi_workspace, cx) =
                cx.add_window_view(|window, cx| MultiWorkspace::test_new(project, window, cx));
            let workspace = multi_workspace
                .read_with(cx, |multi_workspace, _| multi_workspace.workspace().clone());
            let db = cx.update(|_, cx| WorkspaceDb::global(cx));
            let kvp = cx.update(|_, cx| KeyValueStore::global(cx));
            let workspace_id = db.next_id().await.unwrap();
            let items = [1, 2].map(|id| SerializedItem::new("TestItem", id, true, false));
            let center_group = if split {
                group(
                    Axis::Horizontal,
                    items
                        .map(|item| {
                            SerializedPaneGroup::Pane(SerializedPane::new(
                                vec![item.clone()],
                                item.item_id == 2,
                                0,
                            ))
                        })
                        .to_vec(),
                )
            } else {
                SerializedPaneGroup::Pane(SerializedPane::new(items.to_vec(), true, 1))
            };
            let saved = SerializedWorkspace {
                id: workspace_id,
                ..workspace_with(1, &[], center_group, Some("previous"))
            };
            db.save_workspace(saved.clone()).await.unwrap();
            for (item_id, contents) in [(1, "first draft\nλ"), (2, "second draft\n🦀")] {
                kvp.write_kvp(format!("{workspace_id:?}/{item_id}"), contents.to_owned())
                    .await
                    .unwrap();
            }
            cx.update(|_, cx| {
                let descriptor = cx
                    .global_mut::<SerializableItemRegistry>()
                    .descriptors_by_kind
                    .get_mut("TestItem")
                    .unwrap();
                descriptor.deserialize = |_, _, workspace_id, item_id, _, cx| {
                    if item_id == 2 && cx.global::<RestoreFailure>().fail {
                        assert_eq!(cx.global::<RestoreFailure>().completed, [1]);
                        return Task::ready(Err(anyhow::anyhow!(
                            "transport and recovery buffer creation failed"
                        )
                        .context(SavedItemRestoreError)));
                    }
                    let contents = KeyValueStore::global(cx)
                        .read_kvp(&format!("{workspace_id:?}/{item_id}"))
                        .unwrap()
                        .unwrap();
                    let item = cx.new(|cx| persisted_test_item(workspace_id, contents, cx));
                    cx.global_mut::<RestoreFailure>().completed.push(item_id);
                    Task::ready(Ok(Box::new(item) as Box<dyn crate::item::ItemHandle>))
                };
                descriptor.cleanup = |workspace_id, alive_items, _, cx| {
                    cx.global_mut::<RestoreFailure>().cleanups += 1;
                    let kvp = KeyValueStore::global(cx);
                    cx.background_spawn(async move {
                        for item_id in [1, 2] {
                            if !alive_items.contains(&item_id) {
                                kvp.delete_kvp(format!("{workspace_id:?}/{item_id}"))
                                    .await?;
                            }
                        }
                        Ok(())
                    })
                };
            });

            let result = workspace
                .update_in(cx, |workspace, window, cx| {
                    workspace.set_database_id(workspace_id);
                    workspace.load_workspace(saved.clone(), Vec::new(), window, cx)
                })
                .await;
            let Err(error) = result else {
                panic!("restoration unexpectedly succeeded");
            };
            assert!(error.is::<SavedItemRestoreError>());
            workspace.read_with(cx, |workspace, cx| {
                assert!(workspace.is_restoring());
                assert_eq!(workspace.notification_ids().len(), 1);
                assert_eq!(workspace.items_of_type::<TestItem>(cx).count(), 0);
                assert_eq!(workspace.panes.len(), 1);
            });
            workspace
                .update_in(cx, |workspace, window, cx| {
                    workspace.flush_serialization(window, cx)
                })
                .await;
            assert_eq!(
                db.workspace_for_id(workspace_id).unwrap().center_group,
                saved.center_group
            );
            assert_eq!(
                restoration_payloads(&kvp, workspace_id, [1, 2]),
                ["first draft\nλ", "second draft\n🦀"]
            );
            cx.update(|_, cx| {
                let failure = cx.global_mut::<RestoreFailure>();
                assert_eq!(failure.cleanups, 0);
                failure.fail = false;
                failure.completed.clear();
            });

            workspace
                .update_in(cx, |workspace, window, cx| {
                    workspace.load_workspace(saved, Vec::new(), window, cx)
                })
                .await
                .unwrap();
            let runtime_ids = workspace.read_with(cx, |workspace, cx| {
                assert!(!workspace.is_restoring());
                let items = workspace.items_of_type::<TestItem>(cx).collect::<Vec<_>>();
                assert_eq!(
                    items
                        .iter()
                        .map(|item| item.read(cx).state.as_str())
                        .collect::<Vec<_>>(),
                    ["first draft\nλ", "second draft\n🦀"]
                );
                [items[0].entity_id().as_u64(), items[1].entity_id().as_u64()]
            });
            assert_eq!(
                restoration_payloads(&kvp, workspace_id, runtime_ids),
                ["first draft\nλ", "second draft\n🦀"]
            );
            let mut expected_ids = runtime_ids.to_vec();
            expected_ids.sort_unstable();
            assert_eq!(
                db.select_bound::<_, ItemId>(sql!(
                    SELECT item_id FROM items WHERE workspace_id = ? ORDER BY item_id
                ))
                .unwrap()(workspace_id)
                .unwrap(),
                expected_ids
            );
            assert_eq!(cx.update(|_, cx| cx.global::<RestoreFailure>().cleanups), 1);
            for item_id in [1, 2] {
                assert_eq!(
                    kvp.read_kvp(&format!("{workspace_id:?}/{item_id}"))
                        .unwrap(),
                    None
                );
            }
        }
    }

    #[gpui::test]
    async fn test_failed_binding_restores_items_and_retries_window_ownership(
        cx: &mut gpui::TestAppContext,
    ) {
        const SAVED_ITEM_ID: ItemId = i64::MAX as ItemId;

        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Failure {
            None,
            Binding,
            Workspace,
            Item,
        }
        impl Global for Failure {}

        for failure in [Failure::Binding, Failure::Workspace, Failure::Item] {
            let cx = &mut cx.new_app();
            crate::tests::init_test(cx);
            cx.update(|cx| {
                cx.set_global(failure);
                crate::register_serializable_item::<TestItem>(cx);
            });
            let fs = fs::FakeFs::new(cx.executor());
            let project = Project::test(fs, [], cx).await;
            let (multi_workspace, cx) =
                cx.add_window_view(|window, cx| MultiWorkspace::test_new(project, window, cx));
            let workspace = multi_workspace
                .read_with(cx, |multi_workspace, _| multi_workspace.workspace().clone());
            let session_id =
                workspace.read_with(cx, |workspace, _| workspace.session_id().unwrap());
            let window_id =
                multi_workspace.update_in(cx, |_, window, _| window.window_handle().window_id());
            let previous_window_id = WindowId::from(window_id.as_u64().wrapping_add(1));
            let db = cx.update(|_, cx| WorkspaceDb::global(cx));
            let kvp = cx.update(|_, cx| KeyValueStore::global(cx));
            let workspace_id = db.next_id().await.unwrap();
            let sibling_id = db.next_id().await.unwrap();
            let saved = SerializedWorkspace {
                id: workspace_id,
                window_id: Some(previous_window_id.as_u64()),
                ..workspace_with(
                    1,
                    &[],
                    SerializedPaneGroup::Pane(SerializedPane::new(
                        vec![SerializedItem::new("TestItem", SAVED_ITEM_ID, true, false)],
                        true,
                        0,
                    )),
                    Some(&session_id),
                )
            };
            db.save_workspace(saved.clone()).await.unwrap();
            db.save_workspace(SerializedWorkspace {
                id: sibling_id,
                window_id: Some(previous_window_id.as_u64()),
                ..workspace_with(2, &[], empty_pane_group(), Some(&session_id))
            })
            .await
            .unwrap();
            db.adopt_session_workspaces_for_test(
                vec![workspace_id, sibling_id],
                session_id.clone(),
            )
            .await
            .unwrap();
            let saved = db.workspace_for_id(workspace_id).unwrap();
            let previous_group = db.restoring_window(workspace_id).unwrap().unwrap().0;
            kvp.write_kvp(
                format!("{workspace_id:?}/{SAVED_ITEM_ID}"),
                "saved draft".to_owned(),
            )
            .await
            .unwrap();
            cx.update(|_, cx| {
                let descriptor = cx
                    .global_mut::<SerializableItemRegistry>()
                    .descriptors_by_kind
                    .get_mut("TestItem")
                    .unwrap();
                descriptor.deserialize = |_, _, workspace_id, item_id, _, cx| {
                    let kvp = KeyValueStore::global(cx);
                    cx.spawn(async move |_, cx| {
                        let contents = kvp
                            .read_kvp(&format!("{workspace_id:?}/{item_id}"))?
                            .context("missing saved item")?;
                        let item = cx.new(|cx| {
                            let item = persisted_test_item(workspace_id, contents, cx);
                            if *cx.global::<Failure>() == Failure::Item {
                                item.with_serialize(|| {
                                    Some(Box::pin(async {
                                        Err(anyhow::anyhow!("injected item save failure"))
                                    }))
                                })
                            } else {
                                item
                            }
                        });
                        Ok(Box::new(item) as Box<dyn crate::item::ItemHandle>)
                    })
                };
                descriptor.cleanup = |workspace_id, alive_items, _, cx| {
                    let kvp = KeyValueStore::global(cx);
                    cx.background_spawn(async move {
                        if !alive_items.contains(&SAVED_ITEM_ID) {
                            kvp.delete_kvp(format!("{workspace_id:?}/{SAVED_ITEM_ID}"))
                                .await?;
                        }
                        Ok(())
                    })
                };
            });
            if failure != Failure::Item {
                let columns = if failure == Failure::Binding {
                    "session_id, window_id, restoring_window_id"
                } else {
                    "paths"
                };
                db.write(move |connection| {
                    connection.exec(&format!(
                        "CREATE TEMP TRIGGER fail_workspace_binding
                BEFORE UPDATE OF {columns} ON workspaces
                WHEN OLD.workspace_id = {}
                BEGIN
                    SELECT RAISE(FAIL, 'injected workspace binding failure');
                END;",
                        workspace_id.0
                    ))?()
                })
                .await
                .unwrap();
            }

            let app_state = workspace.read_with(cx, |workspace, _| workspace.app_state().clone());
            let create_workspace =
                |multi_workspace: &mut MultiWorkspace,
                 window: &mut gpui::Window,
                 cx: &mut gpui::Context<MultiWorkspace>| {
                    let project = Project::local(
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
                        crate::Workspace::new_unpublished(
                            Some(workspace_id),
                            project,
                            app_state.clone(),
                            window,
                            cx,
                        )
                    });
                    multi_workspace.set_workspace_parent(&workspace, cx);
                    workspace
                };
            let workspace = multi_workspace.update_in(cx, &create_workspace);
            let center_pane = workspace.read_with(cx, |workspace, _| workspace.center.first_pane());
            let restoration = workspace
                .update_in(cx, |workspace, window, cx| {
                    workspace.set_database_id(workspace_id);
                    workspace.load_workspace(saved.clone(), Vec::new(), window, cx)
                })
                .await;
            let error = restoration
                .err()
                .expect("restoration unexpectedly succeeded");
            if failure != Failure::Binding {
                assert_eq!(error.to_string(), "Failed to commit restored workspace");
            }
            let preserved = SerializedWorkspace {
                window_id: if failure == Failure::Binding {
                    saved.window_id
                } else {
                    Some(window_id.as_u64())
                },
                restoring_window_id: if failure == Failure::Binding {
                    saved.restoring_window_id
                } else {
                    None
                },
                ..saved.clone()
            };
            assert_eq!(db.workspace_for_id(workspace_id), Some(preserved.clone()));
            workspace.read_with(cx, |workspace, cx| {
                assert!(workspace.is_restoring());
                assert_eq!(workspace.notification_ids().len(), 0);
                if failure == Failure::Binding {
                    assert_eq!(workspace.center.panes(), vec![&center_pane]);
                    assert_eq!(center_pane.read(cx).items_len(), 0);
                } else {
                    let items = workspace.items_of_type::<TestItem>(cx).collect::<Vec<_>>();
                    assert_eq!(items.len(), 1);
                    assert_eq!(items[0].read(cx).state, "saved draft");
                    assert_eq!(
                        kvp.read_kvp(&format!(
                            "{workspace_id:?}/{}",
                            items[0].entity_id().as_u64()
                        ))
                        .unwrap(),
                        None
                    );
                }
            });
            workspace.update_in(cx, |workspace, window, cx| {
                workspace.serialize_workspace(window, cx);
            });
            cx.run_until_parked();
            cx.executor()
                .advance_clock(crate::SERIALIZATION_THROTTLE_TIME);
            cx.run_until_parked();
            assert_eq!(db.workspace_for_id(workspace_id), Some(preserved.clone()));
            assert_eq!(
                db.restoring_window(workspace_id).unwrap().map(|(id, _)| id),
                (failure == Failure::Binding).then_some(previous_group)
            );
            assert_eq!(
                kvp.read_kvp(&format!("{workspace_id:?}/{SAVED_ITEM_ID}"))
                    .unwrap(),
                Some("saved draft".to_owned())
            );
            if failure != Failure::Item {
                db.write(|connection| {
                    connection.exec(sql!(DROP TRIGGER fail_workspace_binding))?()
                })
                .await
                .unwrap();
            }
            cx.update(|_, cx| cx.set_global(Failure::None));
            drop(workspace);
            let workspace = multi_workspace.update_in(cx, create_workspace);
            workspace
                .update_in(cx, |workspace, window, cx| {
                    workspace.load_workspace(preserved, Vec::new(), window, cx)
                })
                .await
                .unwrap();
            multi_workspace.update_in(cx, |multi_workspace, window, cx| {
                workspace
                    .update(cx, |workspace, cx| workspace.publish_restored(window, cx))
                    .unwrap();
                multi_workspace.activate(workspace.clone(), None, window, cx);
            });
            let restored_item = workspace.read_with(cx, |workspace, cx| {
                assert!(!workspace.is_restoring());
                assert_eq!(workspace.notification_ids().len(), 0);
                let items = workspace.items_of_type::<TestItem>(cx).collect::<Vec<_>>();
                assert_eq!(items.len(), 1);
                assert_eq!(items[0].read(cx).state, "saved draft");
                items[0].clone()
            });
            assert_eq!(
                db.workspace_for_id(workspace_id).unwrap().center_group,
                SerializedPaneGroup::Pane(SerializedPane::new(
                    vec![SerializedItem::new(
                        "TestItem",
                        restored_item.entity_id().as_u64(),
                        true,
                        false,
                    )],
                    true,
                    0,
                ))
            );
            assert_eq!(
                kvp.read_kvp(&format!(
                    "{workspace_id:?}/{}",
                    restored_item.entity_id().as_u64()
                ))
                .unwrap(),
                Some("saved draft".to_owned())
            );
            assert_eq!(
                kvp.read_kvp(&format!("{workspace_id:?}/{SAVED_ITEM_ID}"))
                    .unwrap(),
                None
            );

            multi_workspace
                .update_in(cx, |multi_workspace, window, cx| {
                    multi_workspace.flush_pending_serialization(window, cx)
                })
                .await;
            assert_eq!(db.restoring_window(workspace_id).unwrap(), None);
            assert!(
                db.local_workspace_is_in_window(
                    workspace_id,
                    session_id.clone(),
                    window_id.as_u64()
                )
                .unwrap()
            );
            let new_item =
                cx.new(|cx| persisted_test_item(workspace_id, "new draft".to_owned(), cx));
            workspace.update_in(cx, |workspace, window, cx| {
                workspace.add_item_to_active_pane(
                    Box::new(new_item.clone()),
                    None,
                    true,
                    window,
                    cx,
                );
            });
            restored_item.update(cx, |item, cx| {
                *item = persisted_test_item(workspace_id, "edited saved draft".to_owned(), cx);
                cx.emit(ItemEvent::Edit);
            });
            multi_workspace
                .update_in(cx, |multi_workspace, window, cx| {
                    multi_workspace.flush_pending_serialization(window, cx)
                })
                .await;
            let runtime_ids = [
                restored_item.entity_id().as_u64(),
                new_item.entity_id().as_u64(),
            ];
            let expected = SerializedPaneGroup::Pane(SerializedPane::new(
                vec![
                    SerializedItem::new("TestItem", runtime_ids[0], false, false),
                    SerializedItem::new("TestItem", runtime_ids[1], true, false),
                ],
                true,
                0,
            ));
            assert_eq!(
                db.workspace_for_id(workspace_id).unwrap().center_group,
                expected
            );
            assert_eq!(
                restoration_payloads(&kvp, workspace_id, runtime_ids),
                ["edited saved draft", "new draft"]
            );
            db.complete_window_restoration(
                previous_group,
                session_id.clone(),
                previous_window_id,
                model::MultiWorkspaceState {
                    active_workspace_id: Some(sibling_id),
                    ..model::MultiWorkspaceState::default()
                },
            )
            .await
            .unwrap();
            assert!(
                db.local_workspace_is_in_window(workspace_id, session_id, window_id.as_u64())
                    .unwrap()
            );
            assert_eq!(
                db.workspace_for_id(workspace_id).unwrap().center_group,
                expected
            );
            assert_eq!(db.restoring_window(sibling_id).unwrap(), None);
        }
    }

    #[gpui::test]
    async fn test_serialization_during_restoration_preserves_session(
        cx: &mut gpui::TestAppContext,
    ) {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        enum Operation {
            Serialize,
            Replace,
            FinishAndReplace,
            FinishAndRemove,
        }

        for (poll_restoration, complete_restoration, operation) in [
            (false, false, Operation::Serialize),
            (true, false, Operation::Serialize),
            (true, true, Operation::Serialize),
            (true, false, Operation::Replace),
            (true, false, Operation::FinishAndReplace),
            (true, false, Operation::FinishAndRemove),
        ] {
            let cx = &mut cx.new_app();
            crate::tests::init_test(cx);
            let app_state = cx.update(crate::AppState::test);
            cx.update(|cx| {
                crate::init(app_state, cx);
                crate::register_serializable_item::<TestItem>(cx);
            });
            let fs = fs::FakeFs::new(cx.executor());
            let project = Project::test(fs.clone(), [], cx).await;
            let (multi_workspace, window_cx) =
                cx.add_window_view(|window, cx| MultiWorkspace::test_new(project, window, cx));
            let workspace = multi_workspace.read_with(window_cx, |multi_workspace, _| {
                multi_workspace.workspace().clone()
            });
            let db = window_cx.update(|_, cx| WorkspaceDb::global(cx));
            let workspace_id = db.next_id().await.unwrap();
            let session_id = workspace.update(window_cx, |workspace, _| {
                workspace.set_database_id(workspace_id);
                workspace.session_id().unwrap()
            });
            let items = window_cx.update(|_, cx| [cx.new(TestItem::new), cx.new(TestItem::new)]);
            let saved_ids = [items[1].entity_id().as_u64(), items[0].entity_id().as_u64()];
            let kvp = window_cx.update(|_, cx| KeyValueStore::global(cx));
            for (item_id, contents) in saved_ids
                .into_iter()
                .zip(["first scratch", "second scratch"])
            {
                kvp.write_kvp(format!("{workspace_id:?}/{item_id}"), contents.to_owned())
                    .await
                    .unwrap();
            }
            let center_group = group(
                Axis::Horizontal,
                saved_ids
                    .map(|item_id| {
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![SerializedItem::new("TestItem", item_id, true, false)],
                            item_id == saved_ids[1],
                            usize::from(item_id == saved_ids[0]),
                        ))
                    })
                    .to_vec(),
            );
            let saved = SerializedWorkspace {
                id: workspace_id,
                ..workspace_with(1, &[], center_group.clone(), Some("previous"))
            };
            db.save_workspace(saved).await.unwrap();
            db.adopt_session_workspaces_for_test(vec![workspace_id], session_id.clone())
                .await
                .unwrap();
            let saved = db.workspace_for_id(workspace_id).unwrap();
            let (resume, pending) = oneshot::channel();
            window_cx.update(|_, cx| {
                cx.set_global(PendingRestoration {
                    resume: pending.shared(),
                    blocked_item_id: saved_ids[1],
                    runtime_ids: items.each_ref().map(|item| item.entity_id().as_u64()),
                    items: saved_ids.into_iter().zip(items.clone()).collect(),
                });
                cx.global_mut::<SerializableItemRegistry>()
                    .descriptors_by_kind
                    .get_mut("TestItem")
                    .unwrap()
                    .deserialize = |_, _, workspace_id, item_id, _, cx| {
                    let pending = cx.global::<PendingRestoration>();
                    let resume = pending.resume.clone();
                    let blocked = pending.blocked_item_id == item_id;
                    let item = pending.items[&item_id].clone();
                    let kvp = KeyValueStore::global(cx);
                    cx.spawn(async move |_, cx| {
                        if blocked {
                            resume.await?;
                        }
                        let contents = kvp
                            .read_kvp(&format!("{workspace_id:?}/{item_id}"))?
                            .context("missing saved payload")?;
                        item.update(cx, |item, cx| {
                            *item = persisted_test_item(workspace_id, contents, cx);
                        });
                        Ok(Box::new(item) as Box<dyn crate::item::ItemHandle>)
                    })
                };
                cx.global_mut::<SerializableItemRegistry>()
                    .descriptors_by_kind
                    .get_mut("TestItem")
                    .unwrap()
                    .cleanup = |workspace_id, _, _, cx| {
                    let runtime_ids = cx.global::<PendingRestoration>().runtime_ids;
                    assert_eq!(
                        restoration_payloads(&KeyValueStore::global(cx), workspace_id, runtime_ids),
                        ["first scratch", "second scratch"]
                    );
                    Task::ready(Ok(()))
                };
            });
            let (mut restoration, immediate_save) =
                workspace.update_in(window_cx, |workspace, window, cx| {
                    let restoration = workspace.load_workspace(saved, Vec::new(), window, cx);
                    let save = (!poll_restoration)
                        .then(|| workspace.flush_workspace_and_items(window, cx));
                    (restoration, save)
                });
            if let Some(save) = immediate_save {
                save.await.unwrap();
            } else {
                window_cx.run_until_parked();
                let window = multi_workspace.update_in(window_cx, |_, window, _| {
                    window.window_handle().downcast::<MultiWorkspace>().unwrap()
                });
                let quit = window_cx.spawn(async move |mut cx| {
                    crate::prepare_windows_to_quit(&[window], &mut cx).await
                });
                window_cx.run_until_parked();
                assert_eq!(window_cx.pending_prompt(), None);
                assert_eq!(quit.now_or_never(), Some(true));
                if !complete_restoration {
                    for edited in [false, true] {
                        let item = if edited {
                            workspace.update_in(window_cx, |workspace, window, cx| {
                                workspace.add_item_to_active_pane(
                                    Box::new(items[0].clone()),
                                    None,
                                    true,
                                    window,
                                    cx,
                                );
                            });
                            items[0].update(window_cx, |_, cx| cx.emit(ItemEvent::Edit));
                            items[0].clone()
                        } else {
                            workspace.update_in(window_cx, |workspace, window, cx| {
                                let item = cx.new(|cx| TestItem::new(cx).with_dirty(true));
                                workspace.add_item_to_active_pane(
                                    Box::new(item.clone()),
                                    None,
                                    true,
                                    window,
                                    cx,
                                );
                                item
                            })
                        };
                        let quit = window_cx.spawn(async move |mut cx| {
                            crate::prepare_windows_to_quit(&[window], &mut cx).await
                        });
                        window_cx.run_until_parked();
                        assert!(window_cx.has_pending_prompt(), "edited={edited}");
                        window_cx.simulate_prompt_answer("Cancel");
                        assert!(!quit.await);
                        item.update(window_cx, |item, _| item.is_dirty = false);
                        if edited {
                            workspace.update_in(window_cx, |workspace, window, cx| {
                                workspace.active_pane().update(cx, |pane, cx| {
                                    pane.remove_item(item.entity_id(), false, false, window, cx);
                                });
                            });
                        }
                    }
                }
            }
            assert_eq!(
                restoration_payloads(&kvp, workspace_id, saved_ids),
                ["first scratch", "second scratch"]
            );
            let after_save = db.workspace_for_id(workspace_id).unwrap().center_group;
            assert_eq!(after_save, center_group);
            if complete_restoration {
                resume.send(()).unwrap();
                restoration.await.unwrap();
                let runtime_ids = items.each_ref().map(|item| item.entity_id().as_u64());
                assert_eq!(
                    restoration_payloads(&kvp, workspace_id, runtime_ids),
                    ["first scratch", "second scratch"]
                );
                assert_eq!(
                    items
                        .each_ref()
                        .map(|item| item.read_with(window_cx, |item, _| item.state.clone())),
                    ["first scratch", "second scratch"]
                );
                workspace.update_in(window_cx, |workspace, window, cx| {
                    assert!(!workspace.is_restoring());
                    let item = cx.new(|cx| TestItem::new_deserialized(workspace_id, cx));
                    workspace.add_item_to_active_pane(Box::new(item), None, true, window, cx);
                });
                cx.update(|cx| cx.shutdown());
                let SerializedPaneGroup::Group { children, .. } =
                    db.workspace_for_id(workspace_id).unwrap().center_group
                else {
                    panic!("restored split tree was not saved");
                };
                assert_eq!(
                    children
                        .into_iter()
                        .map(|child| match child {
                            SerializedPaneGroup::Pane(pane) =>
                                (pane.active, pane.children.len(), pane.pinned_count),
                            SerializedPaneGroup::Group { .. } => panic!("unexpected nested split"),
                        })
                        .collect::<Vec<_>>(),
                    vec![(false, 1, 1), (true, 2, 0)]
                );
                continue;
            }
            let mut expected_workspace_ids = vec![workspace_id];
            let mut expected_center_group = center_group.clone();
            let mut payload_ids = saved_ids;
            if operation != Operation::Serialize {
                fs.insert_tree("/session", json!({"replacement": {}})).await;
                window_cx.update(|_, cx| <dyn fs::Fs>::set_global(fs.clone(), cx));
                window_cx.update_global::<settings::SettingsStore, ()>(|store, cx| {
                    store.update_user_settings(cx, |settings| {
                        settings.agent.get_or_insert_default().enabled = Some(true);
                    });
                });
                let finish_during_prompt = operation == Operation::FinishAndReplace
                    || operation == Operation::FinishAndRemove;
                if finish_during_prompt {
                    workspace.update_in(window_cx, |workspace, window, cx| {
                        let item = cx.new(|cx| TestItem::new(cx).with_dirty(true));
                        workspace.add_item_to_active_pane(Box::new(item), None, true, window, cx);
                    });
                }
                let replacement =
                    multi_workspace.update_in(window_cx, |multi_workspace, window, cx| {
                        if operation == Operation::FinishAndRemove {
                            let removal = multi_workspace.remove(
                                [workspace.clone()],
                                RemovalIntent::CloseProject,
                                window,
                                cx,
                            );
                            cx.spawn(async move |multi_workspace, cx| {
                                assert!(removal.await?);
                                multi_workspace.read_with(cx, |multi_workspace, _| {
                                    multi_workspace.workspace().clone()
                                })
                            })
                        } else {
                            multi_workspace.open_project(
                                vec![PathBuf::from("/session/replacement")],
                                crate::OpenMode::Activate,
                                window,
                                cx,
                            )
                        }
                    });
                if finish_during_prompt {
                    window_cx.run_until_parked();
                    assert!(window_cx.has_pending_prompt());
                    resume.send(()).unwrap();
                    (&mut restoration).await.unwrap();
                    assert!(
                        !workspace.read_with(window_cx, |workspace, _| workspace.is_restoring())
                    );
                    expected_center_group = db.workspace_for_id(workspace_id).unwrap().center_group;
                    payload_ids = items.each_ref().map(|item| item.entity_id().as_u64());
                    window_cx.simulate_prompt_answer("Don't Save");
                }
                let replacement = replacement.await.unwrap();
                let replacement_id =
                    replacement.read_with(window_cx, |workspace, _| workspace.database_id());
                if operation == Operation::FinishAndRemove {
                    assert_eq!(replacement_id, None);
                } else {
                    expected_workspace_ids.push(replacement_id.unwrap());
                }
                multi_workspace.read_with(window_cx, |multi_workspace, cx| {
                    assert_eq!(
                        multi_workspace
                            .workspaces()
                            .map(|workspace| workspace.read(cx).database_id())
                            .collect::<Vec<_>>(),
                        vec![replacement_id]
                    );
                });
                assert_eq!(
                    workspace.read_with(window_cx, |workspace, _| workspace.session_id()),
                    Some(session_id.clone())
                );
            }
            cx.update(|cx| cx.shutdown());
            let after_shutdown = db.workspace_for_id(workspace_id).unwrap().center_group;
            assert_eq!(
                restoration_payloads(&kvp, workspace_id, payload_ids),
                ["first scratch", "second scratch"]
            );
            let mut restored = db
                .last_session_workspace_locations(&session_id, None, fs.as_ref())
                .await
                .unwrap()
                .into_iter()
                .map(|workspace| workspace.workspace_id)
                .collect::<Vec<_>>();
            drop(restoration);
            restored.sort_unstable();
            expected_workspace_ids.sort_unstable();
            assert_eq!(
                (after_save, after_shutdown, restored),
                (center_group, expected_center_group, expected_workspace_ids),
                "operation={operation:?}"
            );
        }
    }

    #[gpui::test]
    async fn test_gc_preserves_scratch_inside_window(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db = WorkspaceDb::open_test_db("test_gc_preserves_scratch_inside_window").await;

        db.save_workspace(workspace_with(1, &[], empty_pane_group(), None))
            .await
            .unwrap();

        db.garbage_collect_workspaces(fs.as_ref(), "current", None)
            .await
            .unwrap();
        assert!(
            db.workspace_for_id(WorkspaceId(1)).is_some(),
            "fresh stale workspace must not be deleted before the 7-day window"
        );
    }

    #[gpui::test]
    async fn test_gc_deletes_stale_outside_window(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db = WorkspaceDb::open_test_db("test_gc_deletes_stale_outside_window").await;

        db.save_workspace(workspace_with(1, &[], empty_pane_group(), None))
            .await
            .unwrap();
        db.set_timestamp_for_tests(WorkspaceId(1), "2000-01-01 00:00:00".to_owned())
            .await
            .unwrap();

        db.garbage_collect_workspaces(fs.as_ref(), "current", None)
            .await
            .unwrap();
        assert!(
            db.workspace_for_id(WorkspaceId(1)).is_none(),
            "stale empty workspace older than the retention window must be deleted"
        );
    }

    #[gpui::test]
    async fn test_gc_preserves_directory_workspace_with_missing_path(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_gc_preserves_directory_workspace_with_missing_path")
                .await;

        let missing_dir = PathBuf::from("/missing-project-dir");
        db.save_workspace(workspace_with(
            1,
            &[missing_dir.as_path()],
            empty_pane_group(),
            None,
        ))
        .await
        .unwrap();

        db.garbage_collect_workspaces(fs.as_ref(), "current", None)
            .await
            .unwrap();
        assert!(
            db.workspace_for_id(WorkspaceId(1)).is_some(),
            "a stale workspace within the retention window must be kept"
        );

        db.set_timestamp_for_tests(WorkspaceId(1), "2000-01-01 00:00:00".to_owned())
            .await
            .unwrap();
        db.garbage_collect_workspaces(fs.as_ref(), "current", None)
            .await
            .unwrap();
        assert!(
            db.workspace_for_id(WorkspaceId(1)).is_none(),
            "a stale workspace past the retention window must be deleted"
        );
    }

    #[gpui::test]
    async fn test_gc_preserves_current_and_last_sessions(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db = WorkspaceDb::open_test_db("test_gc_preserves_current_and_last_sessions").await;

        db.save_workspace(workspace_with(1, &[], empty_pane_group(), Some("current")))
            .await
            .unwrap();
        db.save_workspace(workspace_with(2, &[], empty_pane_group(), Some("last")))
            .await
            .unwrap();
        db.save_workspace(workspace_with(3, &[], empty_pane_group(), Some("stale")))
            .await
            .unwrap();

        for id in [1, 2, 3] {
            db.set_timestamp_for_tests(WorkspaceId(id), "2000-01-01 00:00:00".to_owned())
                .await
                .unwrap();
        }

        db.garbage_collect_workspaces(fs.as_ref(), "current", Some("last"))
            .await
            .unwrap();

        assert!(
            db.workspace_for_id(WorkspaceId(1)).is_some(),
            "GC must not delete workspaces belonging to the current session"
        );
        assert!(
            db.workspace_for_id(WorkspaceId(2)).is_some(),
            "GC must not delete workspaces belonging to the last session"
        );
        assert!(
            db.workspace_for_id(WorkspaceId(3)).is_none(),
            "GC should still delete stale workspaces from other sessions"
        );
    }

    #[gpui::test]
    async fn test_gc_deletes_empty_workspace_with_items(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db = WorkspaceDb::open_test_db("test_gc_deletes_empty_workspace_with_items").await;

        db.save_workspace(workspace_with(1, &[], pane_with_items(&[100]), None))
            .await
            .unwrap();
        db.set_timestamp_for_tests(WorkspaceId(1), "2000-01-01 00:00:00".to_owned())
            .await
            .unwrap();

        db.garbage_collect_workspaces(fs.as_ref(), "current", None)
            .await
            .unwrap();
        assert!(
            db.workspace_for_id(WorkspaceId(1)).is_none(),
            "a stale empty-path workspace must be deleted regardless of its items"
        );
    }

    #[gpui::test]
    async fn test_last_session_restores_workspace_with_missing_paths(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_last_session_restores_workspace_with_missing_paths")
                .await;

        let missing = PathBuf::from("/gone/file.rs");
        db.save_workspace(workspace_with(
            1,
            &[missing.as_path()],
            empty_pane_group(),
            Some("s"),
        ))
        .await
        .unwrap();

        let sessions = db
            .last_session_workspace_locations("s", None, fs.as_ref())
            .await
            .unwrap();
        assert!(
            sessions.is_empty(),
            "workspaces whose paths no longer exist on disk must not restore"
        );
    }

    #[gpui::test]
    async fn test_last_session_workspace_locations_remote(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_serializing_workspaces_last_session_workspaces_remote")
                .await;

        let remote_connections = [
            ("host-1", "my-user-1"),
            ("host-2", "my-user-2"),
            ("host-3", "my-user-3"),
            ("host-4", "my-user-4"),
        ]
        .into_iter()
        .map(|(host, user)| async {
            let options = RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host.into(),
                username: Some(user.to_string()),
                ..Default::default()
            });
            db.get_or_create_remote_connection(options.clone())
                .await
                .unwrap();
            options
        })
        .collect::<Vec<_>>();

        let remote_connections = futures::future::join_all(remote_connections).await;

        let workspaces = [
            (1, remote_connections[0].clone(), 9),
            (2, remote_connections[1].clone(), 5),
            (3, remote_connections[2].clone(), 8),
            (4, remote_connections[3].clone(), 2),
        ]
        .into_iter()
        .map(|(id, remote_connection, window_id)| SerializedWorkspace {
            id: WorkspaceId(id),
            paths: PathList::default(),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Remote(remote_connection),
            center_group: Default::default(),
            window_bounds: Default::default(),
            display: Default::default(),
            docks: Default::default(),
            centered_layout: false,
            session_id: Some("one-session".to_owned()),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            window_id: Some(window_id),
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        })
        .collect::<Vec<_>>();

        for workspace in workspaces.iter() {
            db.save_workspace(workspace.clone()).await.unwrap();
        }

        let stack = Some(Vec::from([
            WindowId::from(2), // Top
            WindowId::from(8),
            WindowId::from(5),
            WindowId::from(9), // Bottom
        ]));

        let have = db
            .last_session_workspace_locations("one-session", stack, fs.as_ref())
            .await
            .unwrap();
        assert_eq!(have.len(), 4);
        assert_eq!(
            have[0],
            SessionWorkspace {
                workspace_id: WorkspaceId(4),
                location: SerializedWorkspaceLocation::Remote(remote_connections[3].clone()),
                paths: PathList::default(),
                window_id: Some(WindowId::from(2u64)),
            }
        );
        assert_eq!(
            have[1],
            SessionWorkspace {
                workspace_id: WorkspaceId(3),
                location: SerializedWorkspaceLocation::Remote(remote_connections[2].clone()),
                paths: PathList::default(),
                window_id: Some(WindowId::from(8u64)),
            }
        );
        assert_eq!(
            have[2],
            SessionWorkspace {
                workspace_id: WorkspaceId(2),
                location: SerializedWorkspaceLocation::Remote(remote_connections[1].clone()),
                paths: PathList::default(),
                window_id: Some(WindowId::from(5u64)),
            }
        );
        assert_eq!(
            have[3],
            SessionWorkspace {
                workspace_id: WorkspaceId(1),
                location: SerializedWorkspaceLocation::Remote(remote_connections[0].clone()),
                paths: PathList::default(),
                window_id: Some(WindowId::from(9u64)),
            }
        );
    }

    #[gpui::test]
    async fn test_get_or_create_ssh_project() {
        let db = WorkspaceDb::open_test_db("test_get_or_create_ssh_project").await;

        let host = "example.com".to_string();
        let port = Some(22_u16);
        let user = Some("user".to_string());

        let connection_id = db
            .get_or_create_remote_connection(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host.clone().into(),
                port,
                username: user.clone(),
                ..Default::default()
            }))
            .await
            .unwrap();

        // Test that calling the function again with the same parameters returns the same project
        let same_connection = db
            .get_or_create_remote_connection(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host.clone().into(),
                port,
                username: user.clone(),
                ..Default::default()
            }))
            .await
            .unwrap();

        assert_eq!(connection_id, same_connection);

        // Test with different parameters
        let host2 = "otherexample.com".to_string();
        let port2 = None;
        let user2 = Some("otheruser".to_string());

        let different_connection = db
            .get_or_create_remote_connection(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host2.clone().into(),
                port: port2,
                username: user2.clone(),
                ..Default::default()
            }))
            .await
            .unwrap();

        assert_ne!(connection_id, different_connection);
    }

    #[gpui::test]
    async fn test_get_or_create_ssh_project_with_null_user() {
        let db = WorkspaceDb::open_test_db("test_get_or_create_ssh_project_with_null_user").await;

        let (host, port, user) = ("example.com".to_string(), None, None);

        let connection_id = db
            .get_or_create_remote_connection(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host.clone().into(),
                port,
                username: None,
                ..Default::default()
            }))
            .await
            .unwrap();

        let same_connection_id = db
            .get_or_create_remote_connection(RemoteConnectionOptions::Ssh(SshConnectionOptions {
                host: host.clone().into(),
                port,
                username: user.clone(),
                ..Default::default()
            }))
            .await
            .unwrap();

        assert_eq!(connection_id, same_connection_id);
    }

    #[gpui::test]
    async fn test_get_remote_connections() {
        let db = WorkspaceDb::open_test_db("test_get_remote_connections").await;

        let connections = [
            ("example.com".to_string(), None, None),
            (
                "anotherexample.com".to_string(),
                Some(123_u16),
                Some("user2".to_string()),
            ),
            ("yetanother.com".to_string(), Some(345_u16), None),
        ];

        let mut ids = Vec::new();
        for (host, port, user) in connections.iter() {
            ids.push(
                db.get_or_create_remote_connection(RemoteConnectionOptions::Ssh(
                    SshConnectionOptions {
                        host: host.clone().into(),
                        port: *port,
                        username: user.clone(),
                        ..Default::default()
                    },
                ))
                .await
                .unwrap(),
            );
        }

        let stored_connections = db.remote_connections().unwrap();
        assert_eq!(
            stored_connections,
            [
                (
                    ids[0],
                    RemoteConnectionOptions::Ssh(SshConnectionOptions {
                        host: "example.com".into(),
                        port: None,
                        username: None,
                        ..Default::default()
                    }),
                ),
                (
                    ids[1],
                    RemoteConnectionOptions::Ssh(SshConnectionOptions {
                        host: "anotherexample.com".into(),
                        port: Some(123),
                        username: Some("user2".into()),
                        ..Default::default()
                    }),
                ),
                (
                    ids[2],
                    RemoteConnectionOptions::Ssh(SshConnectionOptions {
                        host: "yetanother.com".into(),
                        port: Some(345),
                        username: None,
                        ..Default::default()
                    }),
                ),
            ]
            .into_iter()
            .collect::<HashMap<_, _>>(),
        );
    }

    #[gpui::test]
    async fn test_simple_split() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("simple_split").await;

        //  -----------------
        //  | 1,2   | 5,6   |
        //  | - - - |       |
        //  | 3,4   |       |
        //  -----------------
        let center_pane = group(
            Axis::Horizontal,
            vec![
                group(
                    Axis::Vertical,
                    vec![
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 1, false, false),
                                SerializedItem::new("Terminal", 2, true, false),
                            ],
                            false,
                            0,
                        )),
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 4, false, false),
                                SerializedItem::new("Terminal", 3, true, false),
                            ],
                            true,
                            0,
                        )),
                    ],
                ),
                SerializedPaneGroup::Pane(SerializedPane::new(
                    vec![
                        SerializedItem::new("Terminal", 5, true, false),
                        SerializedItem::new("Terminal", 6, false, false),
                    ],
                    false,
                    0,
                )),
            ],
        );

        let workspace = default_workspace(&["/tmp"], &center_pane);

        db.save_workspace(workspace.clone()).await.unwrap();

        let new_workspace = db.workspace_for_roots(&["/tmp"]).unwrap();

        assert_eq!(workspace.center_group, new_workspace.center_group);
    }

    #[gpui::test]
    async fn test_cleanup_panes() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_cleanup_panes").await;

        let center_pane = group(
            Axis::Horizontal,
            vec![
                group(
                    Axis::Vertical,
                    vec![
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 1, false, false),
                                SerializedItem::new("Terminal", 2, true, false),
                            ],
                            false,
                            0,
                        )),
                        SerializedPaneGroup::Pane(SerializedPane::new(
                            vec![
                                SerializedItem::new("Terminal", 4, false, false),
                                SerializedItem::new("Terminal", 3, true, false),
                            ],
                            true,
                            0,
                        )),
                    ],
                ),
                SerializedPaneGroup::Pane(SerializedPane::new(
                    vec![
                        SerializedItem::new("Terminal", 5, false, false),
                        SerializedItem::new("Terminal", 6, true, false),
                    ],
                    false,
                    0,
                )),
            ],
        );

        let id = &["/tmp"];

        let mut workspace = default_workspace(id, &center_pane);

        db.save_workspace(workspace.clone()).await.unwrap();

        workspace.center_group = group(
            Axis::Vertical,
            vec![
                SerializedPaneGroup::Pane(SerializedPane::new(
                    vec![
                        SerializedItem::new("Terminal", 1, false, false),
                        SerializedItem::new("Terminal", 2, true, false),
                    ],
                    false,
                    0,
                )),
                SerializedPaneGroup::Pane(SerializedPane::new(
                    vec![
                        SerializedItem::new("Terminal", 4, true, false),
                        SerializedItem::new("Terminal", 3, false, false),
                    ],
                    true,
                    0,
                )),
            ],
        );

        db.save_workspace(workspace.clone()).await.unwrap();

        let new_workspace = db.workspace_for_roots(id).unwrap();

        assert_eq!(workspace.center_group, new_workspace.center_group);
    }

    #[gpui::test]
    async fn test_empty_workspace_window_bounds() {
        zlog::init_test();

        let db = WorkspaceDb::open_test_db("test_empty_workspace_window_bounds").await;
        let id = db.next_id().await.unwrap();

        // Create a workspace with empty paths (empty workspace)
        let empty_paths: &[&str] = &[];
        let display_uuid = Uuid::new_v4();
        let window_bounds = SerializedWindowBounds(WindowBounds::Windowed(Bounds {
            origin: point(px(100.0), px(200.0)),
            size: size(px(800.0), px(600.0)),
        }));

        let workspace = SerializedWorkspace {
            id,
            paths: PathList::new(empty_paths),
            identity_paths: None,
            location: SerializedWorkspaceLocation::Local,
            center_group: Default::default(),
            window_bounds: None,
            display: None,
            docks: Default::default(),
            bookmarks: Default::default(),
            breakpoints: Default::default(),
            centered_layout: false,
            session_id: None,
            window_id: None,
            user_toolchains: Default::default(),
            restoring_window_id: None,
            recent_navigation_history: Default::default(),
        };

        // Save the workspace (this creates the record with empty paths)
        db.save_workspace(workspace.clone()).await.unwrap();

        // Save window bounds separately (as the actual code does via set_window_open_status)
        db.set_window_open_status(id, window_bounds, display_uuid, None)
            .await
            .unwrap();

        // Empty workspaces cannot be retrieved by paths (they'd all match).
        // They must be retrieved by workspace_id.
        assert!(db.workspace_for_roots(empty_paths).is_none());

        // Retrieve using workspace_for_id instead
        let retrieved = db.workspace_for_id(id).unwrap();

        // Verify window bounds were persisted
        assert_eq!(retrieved.id, id);
        assert!(retrieved.window_bounds.is_some());
        assert_eq!(retrieved.window_bounds.unwrap().0, window_bounds.0);
        assert!(retrieved.display.is_some());
        assert_eq!(retrieved.display.unwrap(), display_uuid);
    }

    #[gpui::test]
    async fn test_last_session_workspace_locations_groups_by_window_id(
        cx: &mut gpui::TestAppContext,
    ) {
        let dir1 = tempfile::TempDir::with_prefix("dir1").unwrap();
        let dir2 = tempfile::TempDir::with_prefix("dir2").unwrap();
        let dir3 = tempfile::TempDir::with_prefix("dir3").unwrap();
        let dir4 = tempfile::TempDir::with_prefix("dir4").unwrap();
        let dir5 = tempfile::TempDir::with_prefix("dir5").unwrap();

        let fs = fs::FakeFs::new(cx.executor());
        fs.insert_tree(dir1.path(), json!({})).await;
        fs.insert_tree(dir2.path(), json!({})).await;
        fs.insert_tree(dir3.path(), json!({})).await;
        fs.insert_tree(dir4.path(), json!({})).await;
        fs.insert_tree(dir5.path(), json!({})).await;

        let db =
            WorkspaceDb::open_test_db("test_last_session_workspace_locations_groups_by_window_id")
                .await;

        // Simulate two MultiWorkspace windows each containing two workspaces,
        // plus one single-workspace window:
        //   Window 10: workspace 1, workspace 2
        //   Window 20: workspace 3, workspace 4
        //   Window 30: workspace 5 (only one)
        //
        // On session restore, the caller should be able to group these by
        // window_id to reconstruct the MultiWorkspace windows.
        let workspaces_data: Vec<(i64, &Path, u64)> = vec![
            (1, dir1.path(), 10),
            (2, dir2.path(), 10),
            (3, dir3.path(), 20),
            (4, dir4.path(), 20),
            (5, dir5.path(), 30),
        ];

        for (id, dir, window_id) in &workspaces_data {
            db.save_workspace(SerializedWorkspace {
                id: WorkspaceId(*id),
                paths: PathList::new(&[*dir]),
                identity_paths: None,
                location: SerializedWorkspaceLocation::Local,
                center_group: Default::default(),
                window_bounds: Default::default(),
                display: Default::default(),
                docks: Default::default(),
                centered_layout: false,
                session_id: Some("test-session".to_owned()),
                bookmarks: Default::default(),
                breakpoints: Default::default(),
                window_id: Some(*window_id),
                user_toolchains: Default::default(),
                restoring_window_id: None,
                recent_navigation_history: Default::default(),
            })
            .await
            .unwrap();
        }

        let locations = db
            .last_session_workspace_locations("test-session", None, fs.as_ref())
            .await
            .unwrap();

        // All 5 workspaces should be returned with their window_ids.
        assert_eq!(locations.len(), 5);

        // Every entry should have a window_id so the caller can group them.
        for session_workspace in &locations {
            assert!(
                session_workspace.window_id.is_some(),
                "workspace {:?} missing window_id",
                session_workspace.workspace_id
            );
        }

        // Group by window_id, simulating what the restoration code should do.
        let mut by_window: HashMap<WindowId, Vec<WorkspaceId>> = HashMap::default();
        for session_workspace in &locations {
            if let Some(window_id) = session_workspace.window_id {
                by_window
                    .entry(window_id)
                    .or_default()
                    .push(session_workspace.workspace_id);
            }
        }

        // Should produce 3 windows, not 5.
        assert_eq!(
            by_window.len(),
            3,
            "Expected 3 window groups, got {}: {:?}",
            by_window.len(),
            by_window
        );

        // Window 10 should contain workspaces 1 and 2.
        let window_10 = by_window.get(&WindowId::from(10u64)).unwrap();
        assert_eq!(window_10.len(), 2);
        assert!(window_10.contains(&WorkspaceId(1)));
        assert!(window_10.contains(&WorkspaceId(2)));

        // Window 20 should contain workspaces 3 and 4.
        let window_20 = by_window.get(&WindowId::from(20u64)).unwrap();
        assert_eq!(window_20.len(), 2);
        assert!(window_20.contains(&WorkspaceId(3)));
        assert!(window_20.contains(&WorkspaceId(4)));

        // Window 30 should contain only workspace 5.
        let window_30 = by_window.get(&WindowId::from(30u64)).unwrap();
        assert_eq!(window_30.len(), 1);
        assert!(window_30.contains(&WorkspaceId(5)));
    }

    #[gpui::test]
    async fn test_read_serialized_multi_workspaces_with_state(cx: &mut gpui::TestAppContext) {
        use crate::persistence::model::MultiWorkspaceState;

        // Write multi-workspace state for two windows via the scoped KVP.
        let window_10 = WindowId::from(10u64);
        let window_20 = WindowId::from(20u64);

        let kvp = cx.update(|cx| KeyValueStore::global(cx));

        write_multi_workspace_state(
            &kvp,
            window_10,
            MultiWorkspaceState {
                active_workspace_id: Some(WorkspaceId(2)),
                project_groups: vec![],
                sidebar_open: true,
                sidebar_state: None,
            },
        )
        .await;

        write_multi_workspace_state(
            &kvp,
            window_20,
            MultiWorkspaceState {
                active_workspace_id: Some(WorkspaceId(3)),
                project_groups: vec![],
                sidebar_open: false,
                sidebar_state: None,
            },
        )
        .await;

        // Build session workspaces: two in window 10, one in window 20, one with no window.
        let session_workspaces = vec![
            SessionWorkspace {
                workspace_id: WorkspaceId(1),
                location: SerializedWorkspaceLocation::Local,
                paths: PathList::new(&["/a"]),
                window_id: Some(window_10),
            },
            SessionWorkspace {
                workspace_id: WorkspaceId(2),
                location: SerializedWorkspaceLocation::Local,
                paths: PathList::new(&["/b"]),
                window_id: Some(window_10),
            },
            SessionWorkspace {
                workspace_id: WorkspaceId(3),
                location: SerializedWorkspaceLocation::Local,
                paths: PathList::new(&["/c"]),
                window_id: Some(window_20),
            },
            SessionWorkspace {
                workspace_id: WorkspaceId(4),
                location: SerializedWorkspaceLocation::Local,
                paths: PathList::new(&["/d"]),
                window_id: None,
            },
        ];

        let results = cx.update(|cx| read_serialized_multi_workspaces(session_workspaces, cx));

        // Should produce 3 results: window 10, window 20, and the orphan.
        assert_eq!(results.len(), 3);

        // Window 10: active_workspace_id = 2 picks workspace 2 (paths /b), sidebar open.
        let group_10 = &results[0];
        assert_eq!(group_10.active_workspace.workspace_id, WorkspaceId(2));
        assert_eq!(group_10.state.active_workspace_id, Some(WorkspaceId(2)));
        assert_eq!(group_10.state.sidebar_open, true);

        // Window 20: active_workspace_id = 3 picks workspace 3 (paths /c), sidebar closed.
        let group_20 = &results[1];
        assert_eq!(group_20.active_workspace.workspace_id, WorkspaceId(3));
        assert_eq!(group_20.state.active_workspace_id, Some(WorkspaceId(3)));
        assert_eq!(group_20.state.sidebar_open, false);

        // Orphan: no active_workspace_id, falls back to first workspace (id 4).
        let group_none = &results[2];
        assert_eq!(group_none.active_workspace.workspace_id, WorkspaceId(4));
        assert_eq!(group_none.state.active_workspace_id, None);
        assert_eq!(group_none.state.sidebar_open, false);
    }

    #[gpui::test]
    async fn test_flush_serialization_completes_before_quit(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let project = Project::test(fs.clone(), [], cx).await;

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        let workspace = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());

        let db = cx.update(|_, cx| WorkspaceDb::global(cx));

        // Assign a database_id so serialization will actually persist.
        let workspace_id = db.next_id().await.unwrap();
        workspace.update(cx, |ws, _cx| {
            ws.set_database_id(workspace_id);
        });

        // Mutate some workspace state.
        db.set_centered_layout(workspace_id, true).await.unwrap();

        cx.update(|_, cx| crate::register_serializable_item::<TestItem>(cx));
        let kvp = cx.update(|_, cx| KeyValueStore::global(cx));
        let key = format!("flush-serialization/{workspace_id:?}");
        let (resume_writer, pending_writer) = oneshot::channel();
        let (writer_started, started_writer) = oneshot::channel();
        let item = cx.new(|cx| {
            let pending_writer = Cell::new(Some((writer_started, pending_writer)));
            let key = key.clone();
            TestItem::new(cx).with_serialize(move || {
                let pending_writer = pending_writer.take();
                let key = key.clone();
                Some(Box::pin(async move {
                    let contents = if let Some((started, pending)) = pending_writer {
                        started.send(()).unwrap();
                        pending.await?;
                        "old"
                    } else {
                        "new"
                    };
                    Ok(KeyValueStore::prepare_write_kvp(key, contents.to_owned()))
                }))
            })
        });
        workspace.update_in(cx, |workspace, window, cx| {
            workspace.add_item_to_active_pane(Box::new(item.clone()), None, true, window, cx);
            workspace
                .enqueue_item_serialization(Box::new(item))
                .unwrap();
        });
        started_writer.await.unwrap();

        let task = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.workspace()
                .update(cx, |ws, cx| ws.flush_serialization(window, cx))
        });
        cx.run_until_parked();
        assert!(!task.is_ready());
        assert_eq!(kvp.read_kvp(&key).unwrap(), None);
        resume_writer.send(()).unwrap();
        task.await;
        assert_eq!(kvp.read_kvp(&key).unwrap(), Some("new".to_owned()));

        // Read the workspace back from the DB and verify serialization happened.
        let serialized = db.workspace_for_id(workspace_id);
        assert!(
            serialized.is_some(),
            "flush_serialization should have persisted the workspace to DB"
        );
    }

    #[gpui::test]
    async fn test_pending_serialization_flushed_on_shutdown(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let app_state = cx.update(crate::AppState::test);
        cx.update(|cx| crate::init(app_state.clone(), cx));

        let fs = fs::FakeFs::new(cx.executor());
        let dir = unique_test_dir(&fs, "shutdown-flush").await;
        let project = Project::test(fs.clone(), [dir.as_path()], cx).await;

        let (multi_workspace, vcx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        let workspace = multi_workspace.read_with(vcx, |mw, _| mw.workspace().clone());

        let db = vcx.update(|_, cx| WorkspaceDb::global(cx));
        let workspace_id = db.next_id().await.unwrap();
        workspace.update(vcx, |ws, _cx| {
            ws.set_database_id(workspace_id);
        });

        multi_workspace.update_in(vcx, |multi_workspace, window, cx| {
            multi_workspace.workspace().update(cx, |workspace, cx| {
                workspace.serialize_workspace(window, cx)
            })
        });

        let serialized_paths = db
            .workspace_for_id(workspace_id)
            .expect("next_id should have reserved a row")
            .paths;
        assert_eq!(
            serialized_paths.paths().len(),
            0,
            "the debounced serialization must not have fired yet"
        );

        cx.update(|cx| cx.shutdown());

        let serialized_paths = db
            .workspace_for_id(workspace_id)
            .expect("the workspace row should still exist after shutdown")
            .paths;
        assert_eq!(
            serialized_paths.paths(),
            std::slice::from_ref(&dir),
            "shutdown should flush the pending workspace serialization"
        );
    }

    #[gpui::test]
    async fn test_create_workspace_serialization(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let project = Project::test(fs.clone(), [], cx).await;

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        // Give the first workspace a database_id.
        multi_workspace.update_in(cx, |mw, _, cx| {
            mw.set_random_database_id(cx);
        });

        let window_id =
            multi_workspace.update_in(cx, |_, window, _cx| window.window_handle().window_id());

        // Create a new workspace via the MultiWorkspace API (triggers next_id()).
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.create_test_workspace(window, cx).detach();
        });

        // Let the async next_id() and re-serialization tasks complete.
        cx.run_until_parked();

        // The new workspace should now have a database_id.
        let new_workspace_db_id =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).database_id());
        assert!(
            new_workspace_db_id.is_some(),
            "New workspace should have a database_id after run_until_parked"
        );

        // The multi-workspace state should record it as the active workspace.
        let state = cx.update(|_, cx| read_multi_workspace_state(window_id, cx));
        assert_eq!(
            state.active_workspace_id, new_workspace_db_id,
            "Serialized active_workspace_id should match the new workspace's database_id"
        );

        // The individual workspace row should exist with real data
        // (not just the bare DEFAULT VALUES row from next_id).
        let workspace_id = new_workspace_db_id.unwrap();
        let db = cx.update(|_, cx| WorkspaceDb::global(cx));
        let serialized = db.workspace_for_id(workspace_id);
        assert!(
            serialized.is_some(),
            "Newly created workspace should be fully serialized in the DB after database_id assignment"
        );
    }

    #[gpui::test]
    async fn test_remove_workspace_clears_session_binding(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);
        let fs = fs::FakeFs::new(cx.executor());
        let first_dir = unique_test_dir(&fs, "retained").await;
        let second_dir = unique_test_dir(&fs, "removed").await;
        let first_project = Project::test(fs.clone(), [first_dir.as_path()], cx).await;
        let second_project = Project::test(fs.clone(), [second_dir.as_path()], cx).await;
        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let first_id = db.next_id().await.unwrap();
        let second_id = db.next_id().await.unwrap();
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(first_project, window, cx));
        let second = multi_workspace.update_in(cx, |multi_workspace, window, cx| {
            multi_workspace
                .workspace()
                .update(cx, |workspace, _| workspace.set_database_id(first_id));
            multi_workspace.retain_active_workspace(cx);
            let app_state = multi_workspace.workspace().read(cx).app_state().clone();
            let second = cx.new(|cx| {
                crate::Workspace::new(Some(second_id), second_project, app_state, window, cx)
            });
            multi_workspace.add(second.clone(), window, cx);
            second
        });
        multi_workspace
            .update_in(cx, |multi_workspace, window, cx| {
                multi_workspace.flush_pending_serialization(window, cx)
            })
            .await;
        let binding = multi_workspace.read_with(cx, |multi_workspace, cx| {
            multi_workspace.session_binding(cx)
        });
        assert_eq!(
            db.workspace_binding(first_id).unwrap(),
            Some(binding.clone())
        );
        assert_eq!(
            db.workspace_binding(second_id).unwrap(),
            Some(binding.clone())
        );
        let removed = multi_workspace
            .update_in(cx, |multi_workspace, window, cx| {
                multi_workspace.remove([second], RemovalIntent::CloseProject, window, cx)
            })
            .await
            .unwrap();
        assert!(removed);
        assert_eq!(
            db.workspace_binding(second_id).unwrap(),
            Some((None, None, None))
        );
        assert_eq!(
            db.workspace_binding(first_id).unwrap(),
            Some(binding.clone())
        );
        assert_eq!(
            db.workspace_for_id(second_id).unwrap().paths,
            PathList::new(&[second_dir])
        );
        assert_eq!(
            db.last_session_workspace_locations(&binding.0.unwrap(), None, fs.as_ref())
                .await
                .unwrap()
                .into_iter()
                .map(|workspace| workspace.workspace_id)
                .collect::<Vec<_>>(),
            vec![first_id],
        );
    }

    #[gpui::test]
    async fn test_close_window_quit_app_preserves_all_sidebar_workspaces(
        cx: &mut gpui::TestAppContext,
    ) {
        crate::tests::init_test(cx);

        cx.update_global::<settings::SettingsStore, ()>(|store, cx| {
            store.update_user_settings(cx, |settings| {
                settings.workspace.on_last_window_closed =
                    Some(settings::OnLastWindowClosed::QuitApp);
            });
        });

        let fs = fs::FakeFs::new(cx.executor());
        let dir1 = unique_test_dir(&fs, "close-quit-a").await;
        let dir2 = unique_test_dir(&fs, "close-quit-b").await;
        let project1 = Project::test(fs.clone(), [dir1.as_path()], cx).await;
        let project2 = Project::test(fs.clone(), [dir2.as_path()], cx).await;

        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let ws1_id = db.next_id().await.unwrap();
        let ws2_id = db.next_id().await.unwrap();

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project1.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| {
            mw.open_sidebar(cx);
        });

        let session_id = format!("close-quit-session-{}", Uuid::new_v4());

        let workspace1 = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
        workspace1.update(cx, |ws, _| {
            ws.set_database_id(ws1_id);
            ws.session_id = Some(session_id.clone());
        });

        let workspace2 = multi_workspace.update_in(cx, |mw, window, cx| {
            let workspace = cx.new(|cx| crate::Workspace::test_new(project2.clone(), window, cx));
            workspace.update(cx, |ws, _| {
                ws.set_database_id(ws2_id);
                ws.session_id = Some(session_id.clone());
            });
            mw.add(workspace.clone(), window, cx);
            workspace
        });

        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.activate(workspace2.clone(), None, window, cx);
        });
        cx.run_until_parked();

        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.close_window(&crate::CloseWindow, window, cx);
        });
        cx.run_until_parked();

        let mut restored_ids = db
            .last_session_workspace_locations(&session_id, None, fs.as_ref())
            .await
            .unwrap()
            .into_iter()
            .map(|workspace| workspace.workspace_id)
            .collect::<Vec<_>>();
        restored_ids.sort_by_key(|id| id.0);
        assert_eq!(restored_ids, vec![ws1_id, ws2_id]);
    }

    #[cfg(target_os = "macos")]
    #[gpui::test]
    async fn test_close_window_platform_default_still_removes_from_session(
        cx: &mut gpui::TestAppContext,
    ) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let dir1 = unique_test_dir(&fs, "close-default-a").await;
        let dir2 = unique_test_dir(&fs, "close-default-b").await;
        let project1 = Project::test(fs.clone(), [dir1.as_path()], cx).await;
        let project2 = Project::test(fs.clone(), [dir2.as_path()], cx).await;

        let db = cx.update(|cx| WorkspaceDb::global(cx));
        let ws1_id = db.next_id().await.unwrap();
        let ws2_id = db.next_id().await.unwrap();

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project1.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| {
            mw.open_sidebar(cx);
        });

        let workspace1 = multi_workspace.read_with(cx, |mw, _| mw.workspace().clone());
        let app_state = workspace1.read_with(cx, |workspace, _| workspace.app_state().clone());
        let session_id = app_state
            .session
            .read_with(cx, |session, _| session.id().to_owned());
        workspace1.update(cx, |workspace, _| workspace.set_database_id(ws1_id));

        let workspace2 = multi_workspace.update_in(cx, |mw, window, cx| {
            let workspace = cx.new(|cx| {
                crate::Workspace::new(Some(ws2_id), project2.clone(), app_state, window, cx)
            });
            mw.add(workspace.clone(), window, cx);
            workspace
        });

        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.activate(workspace2.clone(), None, window, cx);
        });
        cx.run_until_parked();

        let (resume_writer, pending_writer) = oneshot::channel();
        let (writer_finished, finished_writer) = oneshot::channel();
        workspace1.update_in(cx, |workspace, window, cx| {
            let serialization = workspace.serialize_workspace_internal(window, cx).unwrap();
            let db = WorkspaceDb::global(cx);
            workspace._serialize_workspace_task = Some(
                cx.background_spawn(async move {
                    pending_writer.await.unwrap();
                    db.write(serialization).await.unwrap();
                    writer_finished.send(()).unwrap();
                })
                .shared(),
            );
        });

        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.close_window(&crate::CloseWindow, window, cx);
        });
        cx.run_until_parked();
        assert_eq!(cx.windows().len(), 1);
        assert_eq!(
            workspace1.read_with(cx, |workspace, _| workspace.session_id()),
            Some(session_id.clone())
        );

        resume_writer.send(()).unwrap();
        finished_writer.await.unwrap();
        cx.run_until_parked();
        assert_eq!(cx.windows().len(), 0);
        for workspace in [&workspace1, &workspace2] {
            let workspace_id = workspace.read_with(cx, |workspace, _| {
                assert_eq!(workspace.session_id(), None);
                workspace.database_id().unwrap()
            });
            assert_eq!(
                db.workspace_binding(workspace_id).unwrap(),
                Some((None, None, None))
            );
        }

        let restored_ids = db
            .last_session_workspace_locations(&session_id, None, fs.as_ref())
            .await
            .unwrap()
            .into_iter()
            .map(|workspace| workspace.workspace_id)
            .collect::<Vec<_>>();
        assert_eq!(restored_ids, Vec::new());
    }

    #[gpui::test]
    async fn test_close_restored_window_removes_unloaded_workspaces(cx: &mut gpui::TestAppContext) {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        enum Operation {
            Close,
            ClosePendingRemote,
            ClosePendingScratch,
            CloseFinishedScratch,
            CloseDuringRestoration,
            CloseLoadedScratch,
            CloseLastWindow,
            CloseLastPendingScratch,
            Collapse,
            Replace,
            Retain,
        }

        for (complete_restoration, operation) in [false, true].into_iter().flat_map(|complete| {
            [
                Operation::Close,
                Operation::CloseLoadedScratch,
                Operation::CloseLastWindow,
                Operation::Collapse,
                Operation::Replace,
                Operation::Retain,
            ]
            .into_iter()
            .chain(
                (!complete)
                    .then_some([
                        Operation::ClosePendingRemote,
                        Operation::ClosePendingScratch,
                        Operation::CloseFinishedScratch,
                        Operation::CloseDuringRestoration,
                        Operation::CloseLastPendingScratch,
                    ])
                    .into_iter()
                    .flatten(),
            )
            .map(move |operation| (complete, operation))
        }) {
            let last_window = matches!(
                operation,
                Operation::CloseLastWindow | Operation::CloseLastPendingScratch
            );
            let restoring_scratch = matches!(
                operation,
                Operation::ClosePendingScratch
                    | Operation::CloseFinishedScratch
                    | Operation::CloseLastPendingScratch
            );
            let scratch = restoring_scratch || operation == Operation::CloseLoadedScratch;
            let cx = &mut cx.new_app();
            crate::tests::init_test(cx);
            cx.update(crate::register_serializable_item::<TestItem>);
            cx.update_global::<settings::SettingsStore, ()>(|store, cx| {
                store.update_user_settings(cx, |settings| {
                    settings.workspace.on_last_window_closed =
                        Some(settings::OnLastWindowClosed::QuitApp);
                    settings.agent.get_or_insert_default().enabled =
                        Some(operation != Operation::Replace);
                });
            });
            let fs = fs::FakeFs::new(cx.executor());
            fs.insert_tree(
                "/session",
                json!({"active": {}, "unloaded": {}, "pending": {}, "replacement": {}}),
            )
            .await;
            cx.update(|cx| <dyn fs::Fs>::set_global(fs.clone(), cx));
            let paths = if scratch {
                Vec::new()
            } else {
                vec![Path::new("/session/active")]
            };
            let project = Project::test(fs.clone(), paths, cx).await;
            let window = cx.add_window(|window, cx| MultiWorkspace::test_new(project, window, cx));
            let workspace = window
                .read_with(cx, |multi_workspace, _| multi_workspace.workspace().clone())
                .unwrap();
            let session_id =
                workspace.read_with(cx, |workspace, _| workspace.session_id().unwrap());
            let db = cx.update(|cx| WorkspaceDb::global(cx));
            let active_id = db.next_id().await.unwrap();
            let unloaded_id = db.next_id().await.unwrap();
            let pending_id = db.next_id().await.unwrap();
            let live_window_id = window.window_id().as_u64();
            for (id, path, saved_window_id) in [
                (active_id, "/session/active", live_window_id.wrapping_add(1)),
                (
                    unloaded_id,
                    "/session/unloaded",
                    live_window_id.wrapping_add(1),
                ),
                (pending_id, "/session/pending", live_window_id),
            ] {
                db.save_workspace(SerializedWorkspace {
                    window_id: Some(saved_window_id),
                    ..workspace_with(
                        id.0 as u64,
                        &if (id == unloaded_id && operation == Operation::ClosePendingRemote)
                            || (id == active_id && scratch)
                        {
                            Vec::new()
                        } else {
                            vec![Path::new(path)]
                        },
                        if id == unloaded_id {
                            pane_with_items(&[1, 2])
                        } else {
                            empty_pane_group()
                        },
                        Some("previous"),
                    )
                })
                .await
                .unwrap();
            }
            let unloaded_pane_group = db.workspace_for_id(unloaded_id).unwrap().center_group;
            db.adopt_session_workspaces_for_test(
                vec![active_id, unloaded_id, pending_id],
                session_id.clone(),
            )
            .await
            .unwrap();
            if operation == Operation::ClosePendingRemote {
                window
                    .update(cx, |multi_workspace, _, cx| {
                        workspace.update(cx, |workspace, _| {
                            assert_eq!(workspace.database_id(), None);
                            workspace.mark_as_remote_connection_placeholder();
                        });
                        multi_workspace.set_restoring_workspace_id(active_id, cx);
                    })
                    .unwrap();
            } else {
                let saved = db.workspace_for_id(active_id).unwrap();
                window
                    .update(cx, |multi_workspace, window, cx| {
                        multi_workspace.set_restoring_workspace_id(active_id, cx);
                        workspace.update(cx, |workspace, cx| {
                            workspace.set_database_id(active_id);
                            workspace.load_workspace(saved, Vec::new(), window, cx)
                        })
                    })
                    .unwrap()
                    .await
                    .unwrap();
            }
            if complete_restoration {
                crate::apply_restored_multiworkspace_state(
                    window,
                    active_id,
                    &model::MultiWorkspaceState {
                        active_workspace_id: Some(active_id),
                        sidebar_open: true,
                        project_groups: ["/session/active", "/session/unloaded"]
                            .map(|path| {
                                model::SerializedProjectGroup::from_group(
                                    &ProjectGroupKey::new(None, PathList::new(&[path])),
                                    true,
                                )
                            })
                            .to_vec(),
                        sidebar_state: None,
                    },
                    &[],
                    fs.clone(),
                    &mut cx.to_async(),
                )
                .await
                .unwrap();
            }
            if !last_window {
                let project = Project::test(fs.clone(), [], cx).await;
                cx.add_window(|window, cx| MultiWorkspace::test_new(project, window, cx));
            }
            let pending_window = db.restoring_window(pending_id).unwrap();
            assert!(crate::prepare_windows_to_quit(&[window], &mut cx.to_async()).await);
            let all_ids = vec![active_id, unloaded_id, pending_id];
            let session_ids = || {
                let mut ids = db
                    .session_workspaces(session_id.clone())
                    .unwrap()
                    .into_iter()
                    .map(|(id, _, _, _)| id)
                    .collect::<Vec<_>>();
                ids.sort();
                ids
            };
            assert_eq!(session_ids(), all_ids);
            let item = cx.new(|cx| TestItem::new(cx).with_dirty(true));
            window
                .update(cx, |_, window, cx| {
                    workspace.update(cx, |workspace, cx| {
                        workspace.add_item_to_active_pane(
                            Box::new(item.clone()),
                            None,
                            true,
                            window,
                            cx,
                        );
                    });
                })
                .unwrap();
            if !matches!(operation, Operation::Collapse | Operation::Retain) {
                let cancelled_open = window
                    .update(cx, |multi_workspace, window, cx| {
                        if operation == Operation::Replace {
                            Some(multi_workspace.open_project(
                                vec![PathBuf::from("/session/replacement")],
                                crate::OpenMode::Activate,
                                window,
                                cx,
                            ))
                        } else {
                            multi_workspace.close_window(&crate::CloseWindow, window, cx);
                            None
                        }
                    })
                    .unwrap();
                cx.run_until_parked();
                assert!(cx.has_pending_prompt());
                cx.simulate_prompt_answer("Cancel");
                cx.run_until_parked();
                if let Some(cancelled_open) = cancelled_open {
                    assert_eq!(cancelled_open.await.unwrap(), workspace);
                }
            }
            assert_eq!(cx.windows().len(), 1 + usize::from(!last_window));
            assert_eq!(session_ids(), all_ids);
            item.update(cx, |item, _| {
                item.is_dirty = matches!(
                    operation,
                    Operation::CloseFinishedScratch
                        | Operation::CloseLoadedScratch
                        | Operation::CloseDuringRestoration
                );
            });
            if scratch {
                window
                    .update(cx, |_, window, cx| {
                        workspace.update(cx, |workspace, cx| {
                            workspace.flush_serialization(window, cx)
                        })
                    })
                    .unwrap()
                    .await;
                let SerializedPaneGroup::Pane(pane) =
                    db.workspace_for_id(active_id).unwrap().center_group
                else {
                    panic!("expected scratch pane");
                };
                assert_eq!(
                    pane.children,
                    vec![SerializedItem::new(
                        "TestItem",
                        item.entity_id().as_u64(),
                        true,
                        false,
                    )]
                );
                if restoring_scratch {
                    workspace.update(cx, |workspace, _| workspace.set_restoring_workspace(true));
                }
            }
            let mut expected_ids = match operation {
                Operation::Close
                | Operation::ClosePendingRemote
                | Operation::ClosePendingScratch
                | Operation::CloseFinishedScratch
                | Operation::CloseDuringRestoration
                | Operation::CloseLoadedScratch
                | Operation::CloseLastWindow
                | Operation::CloseLastPendingScratch => {
                    window
                        .update(cx, |multi_workspace, window, cx| {
                            multi_workspace.close_window(&crate::CloseWindow, window, cx);
                        })
                        .unwrap();
                    cx.run_until_parked();
                    if matches!(
                        operation,
                        Operation::CloseFinishedScratch
                            | Operation::CloseLoadedScratch
                            | Operation::CloseDuringRestoration
                    ) {
                        assert!(cx.has_pending_prompt());
                        if operation == Operation::CloseDuringRestoration {
                            let (group, state) = window
                                .read_with(cx, |multi_workspace, cx| {
                                    (
                                        multi_workspace.restoring_window_id().unwrap(),
                                        multi_workspace.serialized_state(cx),
                                    )
                                })
                                .unwrap();
                            db.complete_window_restoration(
                                group,
                                session_id.clone(),
                                window.window_id(),
                                state,
                            )
                            .await
                            .unwrap();
                            window
                                .update(cx, |multi_workspace, _, _| {
                                    multi_workspace.finish_window_restoration(group)
                                })
                                .unwrap();
                        }
                        workspace.update(cx, |workspace, _| {
                            workspace.set_restoring_workspace(false);
                        });
                        cx.simulate_prompt_answer("Don't Save");
                        cx.run_until_parked();
                    }
                    assert_eq!(cx.windows().len(), usize::from(!last_window));
                    if last_window {
                        all_ids
                    } else if operation == Operation::ClosePendingRemote {
                        vec![unloaded_id, pending_id]
                    } else if restoring_scratch {
                        vec![active_id, pending_id]
                    } else {
                        vec![pending_id]
                    }
                }
                Operation::Collapse => {
                    cx.update_global::<settings::SettingsStore, ()>(|store, cx| {
                        store.update_user_settings(cx, |settings| {
                            settings.agent.get_or_insert_default().enabled = Some(false);
                        });
                    });
                    cx.run_until_parked();
                    vec![active_id, pending_id]
                }
                Operation::Replace | Operation::Retain => {
                    let replacement = window
                        .update(cx, |multi_workspace, window, cx| {
                            multi_workspace.open_project(
                                vec![PathBuf::from("/session/replacement")],
                                crate::OpenMode::Activate,
                                window,
                                cx,
                            )
                        })
                        .unwrap()
                        .await
                        .unwrap();
                    window
                        .read_with(cx, |multi_workspace, _| {
                            assert_eq!(multi_workspace.workspace(), &replacement);
                        })
                        .unwrap();
                    assert_ne!(replacement, workspace);
                    let replacement_id =
                        replacement.read_with(cx, |workspace, _| workspace.database_id().unwrap());
                    if operation == Operation::Replace {
                        vec![pending_id, replacement_id]
                    } else {
                        [all_ids, vec![replacement_id]].concat()
                    }
                }
            };
            if matches!(
                operation,
                Operation::Collapse | Operation::Replace | Operation::Retain
            ) {
                crate::flush_windows_serialization(&[window], &mut cx.to_async()).await;
                assert_eq!(cx.windows().len(), 2);
            }
            expected_ids.sort();
            let mut remaining_ids = db
                .last_session_workspace_locations(&session_id, None, fs.as_ref())
                .await
                .unwrap()
                .into_iter()
                .map(|workspace| workspace.workspace_id)
                .collect::<Vec<_>>();
            remaining_ids.sort();
            assert_eq!(
                remaining_ids, expected_ids,
                "complete_restoration={complete_restoration}, operation={operation:?}"
            );
            assert_eq!(db.restoring_window(pending_id).unwrap(), pending_window);
            assert_eq!(
                db.workspace_for_id(unloaded_id).unwrap().center_group,
                unloaded_pane_group
            );
        }
    }

    #[gpui::test]
    async fn test_restoring_window_ownership_on_open(cx: &mut gpui::TestAppContext) {
        for (same_owner, close, remove_owner) in [
            (false, true, false),
            (true, true, false),
            (false, false, false),
            (true, false, false),
            (true, true, true),
            (true, false, true),
        ] {
            let cx = &mut cx.new_app();
            crate::tests::init_test(cx);
            let app_state = cx.update(crate::AppState::test);
            cx.update(|cx| crate::init(app_state.clone(), cx));
            app_state
                .fs
                .as_fake()
                .insert_tree(
                    "/session",
                    json!({"sibling": {}, "unloaded": {}, "new": {}}),
                )
                .await;
            let session_id = cx.update(|cx| app_state.session.read(cx).id().to_owned());
            let db = cx.update(|cx| WorkspaceDb::global(cx));
            let owner_id = db.next_id().await.unwrap();
            let sibling_id = db.next_id().await.unwrap();
            let unloaded_id = db.next_id().await.unwrap();
            for (workspace_id, paths) in [
                (owner_id, Vec::new()),
                (sibling_id, vec![Path::new("/session/sibling")]),
                (unloaded_id, vec![Path::new("/session/unloaded")]),
            ] {
                db.save_workspace(SerializedWorkspace {
                    window_id: Some(10),
                    ..workspace_with(
                        workspace_id.0 as u64,
                        &paths,
                        empty_pane_group(),
                        Some("previous"),
                    )
                })
                .await
                .unwrap();
            }
            let mut state = model::MultiWorkspaceState {
                active_workspace_id: Some(owner_id),
                sidebar_open: true,
                sidebar_state: Some("{}".to_owned()),
                project_groups: ["/session/sibling", "/session/unloaded"]
                    .map(|path| {
                        model::SerializedProjectGroup::from_group(
                            &ProjectGroupKey::new(None, PathList::new(&[path])),
                            path == "/session/unloaded",
                        )
                    })
                    .to_vec(),
            };
            let kvp = cx.update(|cx| KeyValueStore::global(cx));
            write_multi_workspace_state(&kvp, WindowId::from(10u64), state.clone()).await;
            db.adopt_session_workspaces_for_test(
                vec![owner_id, sibling_id, unloaded_id],
                session_id.clone(),
            )
            .await
            .unwrap();
            let restoring_group = db.restoring_window(owner_id).unwrap();
            let owner_window = cx
                .update(|cx| crate::open_workspace_by_id(owner_id, app_state.clone(), None, cx))
                .await
                .unwrap();
            let owner_workspace = owner_window
                .read_with(cx, |multi_workspace, _| multi_workspace.workspace().clone())
                .unwrap();
            let sibling = cx
                .update(|cx| {
                    crate::Workspace::new_local(
                        vec![PathBuf::from("/session/sibling")],
                        app_state.clone(),
                        same_owner.then_some(owner_window),
                        None,
                        None,
                        if same_owner {
                            crate::OpenMode::Activate
                        } else {
                            crate::OpenMode::Add
                        },
                        cx,
                    )
                })
                .await
                .unwrap();
            assert_eq!(
                sibling
                    .workspace
                    .read_with(cx, |workspace, _| workspace.database_id()),
                Some(sibling_id)
            );
            assert_eq!(sibling.window == owner_window, same_owner);
            if same_owner {
                owner_window
                    .update(cx, |multi_workspace, window, cx| {
                        multi_workspace.activate(owner_workspace.clone(), None, window, cx);
                        multi_workspace.activate(sibling.workspace.clone(), None, window, cx);
                    })
                    .unwrap();
            }
            if remove_owner {
                assert!(
                    owner_window
                        .update(cx, |multi_workspace, window, cx| {
                            multi_workspace.remove(
                                [owner_workspace],
                                RemovalIntent::CloseProject,
                                window,
                                cx,
                            )
                        })
                        .unwrap()
                        .await
                        .unwrap()
                );
                cx.run_until_parked();
                assert_eq!(db.workspace_for_id(owner_id).unwrap().session_id, None);
            }
            if close {
                let project = Project::test(app_state.fs.clone(), [], cx).await;
                cx.add_window(|window, cx| {
                    let workspace = cx.new(|cx| {
                        crate::Workspace::new(None, project, app_state.clone(), window, cx)
                    });
                    MultiWorkspace::new(workspace, window, cx)
                });
                sibling
                    .window
                    .update(cx, |multi_workspace, window, cx| {
                        multi_workspace.close_window(&crate::CloseWindow, window, cx);
                    })
                    .unwrap();
                cx.run_until_parked();
                let mut remaining = db
                    .session_workspaces(session_id.clone())
                    .unwrap()
                    .into_iter()
                    .map(|(workspace_id, _, _, _)| workspace_id)
                    .collect::<Vec<_>>();
                remaining.sort_unstable();
                assert_eq!(
                    remaining,
                    if same_owner {
                        Vec::new()
                    } else {
                        vec![owner_id, unloaded_id]
                    },
                    "same_owner={same_owner}, remove_owner={remove_owner}"
                );
                assert_eq!(
                    db.restoring_window(unloaded_id).unwrap(),
                    if same_owner { None } else { restoring_group }
                );
            } else {
                let new_workspace_id = if same_owner {
                    let workspace = owner_window
                        .update(cx, |multi_workspace, window, cx| {
                            multi_workspace.open_project(
                                vec![PathBuf::from("/session/new")],
                                crate::OpenMode::Activate,
                                window,
                                cx,
                            )
                        })
                        .unwrap()
                        .await
                        .unwrap();
                    let workspace_id =
                        workspace.read_with(cx, |workspace, _| workspace.database_id().unwrap());
                    state.active_workspace_id = Some(workspace_id);
                    state.project_groups.insert(
                        0,
                        model::SerializedProjectGroup::from_group(
                            &ProjectGroupKey::new(None, PathList::new(&["/session/new"])),
                            true,
                        ),
                    );
                    Some(workspace_id)
                } else {
                    None
                };
                let restoring_group =
                    restoring_group.map(|(id, _)| (id, serde_json::to_string(&state).unwrap()));
                let windows = cx
                    .windows()
                    .into_iter()
                    .filter_map(|window| window.downcast::<MultiWorkspace>())
                    .collect::<Vec<_>>();
                assert!(crate::prepare_windows_to_quit(&windows, &mut cx.to_async()).await);
                let locations = db
                    .last_session_workspace_locations(&session_id, None, app_state.fs.as_ref())
                    .await
                    .unwrap();
                let mut workspace_ids = locations
                    .iter()
                    .map(|workspace| workspace.workspace_id)
                    .collect::<Vec<_>>();
                workspace_ids.sort_unstable();
                let mut expected_ids = vec![owner_id, sibling_id, unloaded_id];
                expected_ids.retain(|id| !remove_owner || *id != owner_id);
                expected_ids.extend(new_workspace_id);
                assert_eq!(workspace_ids, expected_ids);
                let restored = cx.update(|cx| read_serialized_multi_workspaces(locations, cx));
                assert_eq!(restored.len(), if same_owner { 1 } else { 2 });
                if let Some(new_workspace_id) = new_workspace_id {
                    assert_eq!(restored[0].active_workspace.workspace_id, new_workspace_id);
                    assert_eq!(
                        db.restoring_window(new_workspace_id).unwrap(),
                        restoring_group
                    );
                }
                assert_eq!(
                    db.restoring_window(owner_id).unwrap(),
                    if remove_owner {
                        None
                    } else {
                        restoring_group.clone()
                    }
                );
                assert_eq!(db.restoring_window(unloaded_id).unwrap(), restoring_group);
                assert_eq!(
                    db.restoring_window(sibling_id).unwrap(),
                    if same_owner { restoring_group } else { None }
                );
                crate::apply_restored_multiworkspace_state(
                    owner_window,
                    owner_id,
                    &state,
                    &[],
                    app_state.fs.clone(),
                    &mut cx.to_async(),
                )
                .await
                .unwrap();
                assert_eq!(db.restoring_window(owner_id).unwrap(), None);
                assert_eq!(db.restoring_window(sibling_id).unwrap(), None);
                assert_eq!(db.restoring_window(unloaded_id).unwrap(), None);
                assert_eq!(
                    db.workspace_for_id(unloaded_id).unwrap().window_id,
                    Some(owner_window.window_id().as_u64())
                );
                assert_eq!(
                    db.workspace_for_id(sibling_id).unwrap().window_id,
                    Some(sibling.window.window_id().as_u64())
                );
                if let Some(new_workspace_id) = new_workspace_id {
                    assert_eq!(db.restoring_window(new_workspace_id).unwrap(), None);
                    assert_eq!(
                        db.workspace_for_id(new_workspace_id).unwrap().window_id,
                        Some(owner_window.window_id().as_u64())
                    );
                }
            }
        }
    }

    #[gpui::test]
    async fn test_create_workspace_bounds_observer_uses_fresh_id(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let project = Project::test(fs.clone(), [], cx).await;

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        multi_workspace.update_in(cx, |mw, _, cx| {
            mw.set_random_database_id(cx);
        });

        let task =
            multi_workspace.update_in(cx, |mw, window, cx| mw.create_test_workspace(window, cx));
        task.await;

        let new_workspace_db_id =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).database_id());
        assert!(
            new_workspace_db_id.is_some(),
            "After run_until_parked, the workspace should have a database_id"
        );

        let workspace_id = new_workspace_db_id.unwrap();

        let db = cx.update(|_, cx| WorkspaceDb::global(cx));

        assert!(
            db.workspace_for_id(workspace_id).is_some(),
            "The workspace row should exist in the DB"
        );

        cx.simulate_resize(gpui::size(px(1024.0), px(768.0)));

        // Advance the clock past the 100ms debounce timer so the bounds
        // observer task fires
        cx.executor().advance_clock(Duration::from_millis(200));
        cx.run_until_parked();

        let serialized = db
            .workspace_for_id(workspace_id)
            .expect("workspace row should still exist");
        assert!(
            serialized.window_bounds.is_some(),
            "The bounds observer should write bounds for the workspace's real DB ID, \
             even when the workspace was created via create_workspace (where the ID \
             is assigned asynchronously after construction)."
        );
    }

    #[gpui::test]
    async fn test_flush_serialization_writes_bounds(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let dir = tempfile::TempDir::with_prefix("flush_bounds_test").unwrap();
        fs.insert_tree(dir.path(), json!({})).await;

        let project = Project::test(fs.clone(), [dir.path()], cx).await;

        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        let db = cx.update(|_, cx| WorkspaceDb::global(cx));
        let workspace_id = db.next_id().await.unwrap();
        multi_workspace.update_in(cx, |mw, _, cx| {
            mw.workspace().update(cx, |ws, _cx| {
                ws.set_database_id(workspace_id);
            });
        });

        let task = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.workspace()
                .update(cx, |ws, cx| ws.flush_serialization(window, cx))
        });
        task.await;

        let after = db
            .workspace_for_id(workspace_id)
            .expect("workspace row should exist after flush_serialization");
        assert!(
            !after.paths.is_empty(),
            "flush_serialization should have written paths via save_workspace"
        );
        assert!(
            after.window_bounds.is_some(),
            "flush_serialization should ensure window bounds are persisted to the DB \
             before the process exits."
        );
    }

    #[gpui::test]
    async fn test_empty_window_without_items_stays_in_session(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let project = Project::test(fs.clone(), [], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        let db = cx.update(|_, cx| WorkspaceDb::global(cx));
        let workspace_id = db.next_id().await.unwrap();
        let session_id = multi_workspace
            .update_in(cx, |multi_workspace, _, cx| {
                multi_workspace.workspace().update(cx, |workspace, _| {
                    workspace.set_database_id(workspace_id);
                    workspace.session_id()
                })
            })
            .unwrap();

        multi_workspace
            .update_in(cx, |multi_workspace, window, cx| {
                multi_workspace.workspace().update(cx, |workspace, cx| {
                    workspace.flush_serialization(window, cx)
                })
            })
            .await;

        let restored = db
            .last_session_workspace_locations(&session_id, None, fs.as_ref())
            .await
            .unwrap();
        assert_eq!(
            restored
                .iter()
                .map(|workspace| workspace.workspace_id)
                .collect::<Vec<_>>(),
            vec![workspace_id]
        );
    }

    #[gpui::test]
    async fn test_window_with_last_folder_removed_reopens_empty(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        fs.insert_tree("/project", json!({ "main.rs": "" })).await;
        let project = Project::test(fs.clone(), [Path::new("/project")], cx).await;
        let (multi_workspace, cx) =
            cx.add_window_view(|window, cx| MultiWorkspace::test_new(project.clone(), window, cx));

        let db = cx.update(|_, cx| WorkspaceDb::global(cx));
        let workspace_id = db.next_id().await.unwrap();
        let session_id = multi_workspace
            .update_in(cx, |multi_workspace, _, cx| {
                multi_workspace.workspace().update(cx, |workspace, _| {
                    workspace.set_database_id(workspace_id);
                    workspace.session_id()
                })
            })
            .unwrap();
        multi_workspace
            .update_in(cx, |multi_workspace, window, cx| {
                multi_workspace.workspace().update(cx, |workspace, cx| {
                    workspace.flush_serialization(window, cx)
                })
            })
            .await;
        assert_eq!(
            db.workspace_for_id(workspace_id).unwrap().paths,
            PathList::new(&[Path::new("/project")])
        );

        let worktree_id = project.read_with(cx, |project, cx| {
            project.worktrees(cx).next().unwrap().read(cx).id()
        });
        project.update(cx, |project, cx| project.remove_worktree(worktree_id, cx));
        multi_workspace
            .update_in(cx, |multi_workspace, window, cx| {
                multi_workspace.workspace().update(cx, |workspace, cx| {
                    workspace.flush_serialization(window, cx)
                })
            })
            .await;

        assert_eq!(
            db.workspace_for_id(workspace_id).unwrap().paths,
            PathList::default()
        );
        let restored = db
            .last_session_workspace_locations(&session_id, None, fs.as_ref())
            .await
            .unwrap();
        assert_eq!(
            restored
                .iter()
                .map(|workspace| (workspace.workspace_id, workspace.paths.clone()))
                .collect::<Vec<_>>(),
            vec![(workspace_id, PathList::default())]
        );
    }

    #[gpui::test]
    async fn test_recent_workspace_identity_deduplication(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());

        // Main repo with a linked worktree entry
        fs.insert_tree(
            "/repo",
            json!({
                ".git": {
                    "worktrees": {
                        "feature": {
                            "commondir": "../../",
                            "HEAD": "ref: refs/heads/feature"
                        }
                    }
                },
                "src": { "main.rs": "" }
            }),
        )
        .await;

        // Linked worktree checkout pointing back to /repo
        fs.insert_tree(
            "/worktree",
            json!({
                ".git": "gitdir: /repo/.git/worktrees/feature",
                "src": { "main.rs": "" }
            }),
        )
        .await;

        // A plain non-git project
        fs.insert_tree(
            "/plain-project",
            json!({
                "src": { "main.rs": "" }
            }),
        )
        .await;

        // Another normal git repo (used in mixed-path entry)
        fs.insert_tree(
            "/other-repo",
            json!({
                ".git": {},
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        let t0 = Utc::now() - chrono::Duration::hours(4);
        let t1 = Utc::now() - chrono::Duration::hours(3);
        let t2 = Utc::now() - chrono::Duration::hours(2);
        let t3 = Utc::now() - chrono::Duration::hours(1);

        let workspaces = vec![
            local_recent_workspace(WorkspaceId(1), PathList::new(&["/repo"]), t0, fs.as_ref())
                .await,
            local_recent_workspace(
                WorkspaceId(2),
                PathList::new(&["/worktree"]),
                t1,
                fs.as_ref(),
            )
            .await,
            local_recent_workspace(
                WorkspaceId(3),
                PathList::new(&["/other-repo", "/worktree"]),
                t2,
                fs.as_ref(),
            )
            .await,
            local_recent_workspace(
                WorkspaceId(4),
                PathList::new(&["/plain-project"]),
                t3,
                fs.as_ref(),
            )
            .await,
        ];

        let result = dedupe_recent_workspaces(workspaces);

        // Should have 3 entries: #1 and #2 deduped into one, plus #3 and #4.
        assert_eq!(result.len(), 3);

        // First entry: /repo — deduplicated from #1 and #2.
        // Keeps the position of #1 (first seen), but with #2's later timestamp.
        assert_eq!(result[0].identity_paths.paths(), &[PathBuf::from("/repo")]);
        assert_eq!(result[0].timestamp, t1);

        // Second entry: mixed-path workspace with worktree resolved.
        // /worktree → /repo, so paths become [/other-repo, /repo] (sorted).
        assert_eq!(
            result[1].identity_paths.paths(),
            &[PathBuf::from("/other-repo"), PathBuf::from("/repo")]
        );
        assert_eq!(result[1].workspace_id, WorkspaceId(3));

        // Third entry: non-git project, unchanged.
        assert_eq!(
            result[2].identity_paths.paths(),
            &[PathBuf::from("/plain-project")]
        );
        assert_eq!(result[2].workspace_id, WorkspaceId(4));
    }

    #[gpui::test]
    async fn test_recent_workspace_identity_for_bare_repo(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());

        // Bare repo at /foo/.bare (commondir doesn't end with .git)
        fs.insert_tree(
            "/foo/.bare",
            json!({
                "worktrees": {
                    "my-feature": {
                        "commondir": "../../",
                        "HEAD": "ref: refs/heads/my-feature"
                    }
                }
            }),
        )
        .await;

        // Linked worktree whose commondir resolves to a bare repo (/foo/.bare)
        fs.insert_tree(
            "/foo/my-feature",
            json!({
                ".git": "gitdir: /foo/.bare/worktrees/my-feature",
                "src": { "main.rs": "" }
            }),
        )
        .await;

        let t0 = Utc::now();

        let result = local_recent_workspace(
            WorkspaceId(1),
            PathList::new(&["/foo/my-feature"]),
            t0,
            fs.as_ref(),
        )
        .await;

        // Bare-backed worktrees should resolve to the repo identity path, which
        // is the parent directory users think of as the project root.
        assert_eq!(result.identity_paths.paths(), &[PathBuf::from("/foo")]);
    }

    #[gpui::test]
    async fn test_recent_workspace_identity_for_submodule(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());

        // Superproject `/Foo` with a submodule `Bar`. A submodule's `.git` is a
        // file pointing into the superproject's `.git/modules/<name>` directory,
        // structurally like a linked worktree's `.git` file.
        fs.insert_tree(
            "/Foo",
            json!({
                ".git": {
                    "modules": {
                        "Bar": {
                            "HEAD": "ref: refs/heads/main"
                        }
                    }
                },
                "Bar": {
                    ".git": "gitdir: ../.git/modules/Bar\n",
                    "src": { "main.rs": "" }
                },
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        let t0 = Utc::now();

        let result = local_recent_workspace(
            WorkspaceId(1),
            PathList::new(&["/Foo/Bar"]),
            t0,
            fs.as_ref(),
        )
        .await;

        // Submodules are independent projects: their identity is their own
        // working directory, not the superproject's `.git/modules/<name>`.
        assert_eq!(result.identity_paths.paths(), &[PathBuf::from("/Foo/Bar")]);
    }

    #[gpui::test]
    async fn test_recent_workspace_identity_deduplicates_main_and_linked_worktree(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());

        fs.insert_tree(
            "/the-project",
            json!({
                ".git": "gitdir: ./.bare\n",
                ".bare": {
                    "worktrees": {
                        "feature-a": {
                            "commondir": "../../",
                            "HEAD": "ref: refs/heads/feature-a"
                        }
                    }
                },
                "src": { "main.rs": "" }
            }),
        )
        .await;

        fs.insert_tree(
            "/the-project/feature-a",
            json!({
                ".git": "gitdir: ../.bare/worktrees/feature-a\n",
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        let t0 = Utc::now() - chrono::Duration::hours(1);
        let t1 = Utc::now();
        let workspaces = vec![
            local_recent_workspace(
                WorkspaceId(1),
                PathList::new(&["/the-project"]),
                t0,
                fs.as_ref(),
            )
            .await,
            local_recent_workspace(
                WorkspaceId(2),
                PathList::new(&["/the-project/feature-a"]),
                t1,
                fs.as_ref(),
            )
            .await,
        ];

        let result = dedupe_recent_workspaces(workspaces);

        assert_eq!(result.len(), 1);
        assert_eq!(
            result[0].identity_paths.paths(),
            &[PathBuf::from("/the-project")]
        );
        assert_eq!(result[0].workspace_id, WorkspaceId(2));
        assert_eq!(result[0].timestamp, t1);
    }

    #[gpui::test]
    async fn test_recent_project_workspaces_preserve_reopen_paths(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_recent_project_workspaces_preserve_reopen_paths").await;

        fs.insert_tree(
            "/the-project",
            json!({
                ".git": "gitdir: ./.bare\n",
                ".bare": {
                    "worktrees": {
                        "feature-a": {
                            "commondir": "../../",
                            "HEAD": "ref: refs/heads/feature-a"
                        }
                    }
                },
                "src": { "main.rs": "" }
            }),
        )
        .await;

        fs.insert_tree(
            "/the-project/feature-a",
            json!({
                ".git": "gitdir: ../.bare/worktrees/feature-a\n",
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        db.save_workspace(workspace_with(
            1,
            &[Path::new("/the-project")],
            empty_pane_group(),
            None,
        ))
        .await
        .unwrap();
        db.save_workspace(workspace_with(
            2,
            &[Path::new("/the-project/feature-a")],
            empty_pane_group(),
            None,
        ))
        .await
        .unwrap();
        db.set_timestamp_for_tests(WorkspaceId(1), "2024-01-01 00:00:00".to_owned())
            .await
            .unwrap();
        db.set_timestamp_for_tests(WorkspaceId(2), "2024-01-01 00:00:01".to_owned())
            .await
            .unwrap();

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();

        assert_eq!(recents.len(), 1);
        assert_eq!(recents[0].workspace_id, WorkspaceId(2));
        assert_eq!(
            recents[0].paths.paths(),
            &[PathBuf::from("/the-project/feature-a")]
        );
        assert_eq!(
            recents[0].identity_paths.paths(),
            &[PathBuf::from("/the-project")]
        );
    }

    #[gpui::test]
    async fn test_recent_project_workspaces_remote_identity_hint(cx: &mut gpui::TestAppContext) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_recent_project_workspaces_remote_identity_hint").await;

        let workspace = remote_workspace_with(1, "example.com", &[Path::new("/repo/feature-a")]);
        db.save_workspace(SerializedWorkspace {
            identity_paths: Some(PathList::new(&["/repo"])),
            ..workspace
        })
        .await
        .unwrap();

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();

        assert_eq!(recents.len(), 1);
        assert_eq!(
            recents[0].paths.paths(),
            &[PathBuf::from("/repo/feature-a")]
        );
        assert_eq!(recents[0].identity_paths.paths(), &[PathBuf::from("/repo")]);
    }

    #[gpui::test]
    async fn test_recent_project_workspaces_remote_paths_do_not_use_local_fs_identity(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        let db = WorkspaceDb::open_test_db(
            "test_recent_project_workspaces_remote_paths_do_not_use_local_fs_identity",
        )
        .await;

        fs.insert_tree(
            "/repo",
            json!({
                ".git": "gitdir: ./.bare\n",
                ".bare": {
                    "worktrees": {
                        "feature-a": {
                            "commondir": "../../",
                            "HEAD": "ref: refs/heads/feature-a"
                        }
                    }
                },
                "src": { "main.rs": "" }
            }),
        )
        .await;
        fs.insert_tree(
            "/repo/feature-a",
            json!({
                ".git": "gitdir: ../.bare/worktrees/feature-a\n",
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        db.save_workspace(remote_workspace_with(
            1,
            "example.com",
            &[Path::new("/repo/feature-a")],
        ))
        .await
        .unwrap();

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();

        assert_eq!(recents.len(), 1);
        assert_eq!(
            recents[0].identity_paths.paths(),
            &[PathBuf::from("/repo/feature-a")]
        );
    }

    #[gpui::test]
    async fn test_recent_project_workspaces_do_not_dedupe_remote_hosts(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_recent_project_workspaces_do_not_dedupe_remote_hosts")
                .await;

        db.save_workspace(remote_workspace_with(1, "host-a", &[Path::new("/repo")]))
            .await
            .unwrap();
        db.save_workspace(remote_workspace_with(2, "host-b", &[Path::new("/repo")]))
            .await
            .unwrap();
        db.set_timestamp_for_tests(WorkspaceId(1), "2024-01-01 00:00:00".to_owned())
            .await
            .unwrap();
        db.set_timestamp_for_tests(WorkspaceId(2), "2024-01-01 00:00:01".to_owned())
            .await
            .unwrap();

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();

        assert_eq!(recents.len(), 2);
        assert_eq!(recents[0].workspace_id, WorkspaceId(2));
        assert_eq!(recents[1].workspace_id, WorkspaceId(1));
    }

    #[gpui::test]
    async fn test_remove_recent_workspace_group_preserves_session_rows(
        cx: &mut gpui::TestAppContext,
    ) {
        let fs = fs::FakeFs::new(cx.executor());
        let db =
            WorkspaceDb::open_test_db("test_remove_recent_workspace_group_preserves_session_rows")
                .await;

        fs.insert_tree(
            "/the-group",
            json!({
                ".git": "gitdir: ./.bare\n",
                ".bare": {
                    "worktrees": {
                        "feature-a": {
                            "commondir": "../../",
                            "HEAD": "ref: refs/heads/feature-a"
                        }
                    }
                },
                "src": { "main.rs": "" }
            }),
        )
        .await;

        fs.insert_tree(
            "/the-group/feature-a",
            json!({
                ".git": "gitdir: ../.bare/worktrees/feature-a\n",
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        db.save_workspace(SerializedWorkspace {
            identity_paths: Some(PathList::new(&["/the-group"])),
            ..workspace_with(1, &[Path::new("/the-group")], empty_pane_group(), None)
        })
        .await
        .unwrap();
        db.save_workspace(SerializedWorkspace {
            identity_paths: Some(PathList::new(&["/the-group"])),
            ..workspace_with(
                2,
                &[Path::new("/the-group/feature-a")],
                empty_pane_group(),
                None,
            )
        })
        .await
        .unwrap();
        db.set_timestamp_for_tests(WorkspaceId(1), "2024-01-01 00:00:00".to_owned())
            .await
            .unwrap();
        db.set_timestamp_for_tests(WorkspaceId(2), "2024-01-01 00:00:01".to_owned())
            .await
            .unwrap();

        let recents = db.recent_project_workspaces(fs.as_ref()).await.unwrap();
        assert_eq!(recents.len(), 1);

        db.set_session_binding(WorkspaceId(1), Some("current".to_owned()), Some(1))
            .await
            .unwrap();
        db.set_session_binding(WorkspaceId(2), Some("previous".to_owned()), Some(2))
            .await
            .unwrap();
        let saved = db.workspace_for_id(WorkspaceId(1)).unwrap();
        let deleted = db.delete_recent_workspace_group(&recents[0]).await.unwrap();
        assert_eq!(deleted, vec![WorkspaceId(2), WorkspaceId(1)]);
        db.save_workspace(saved.clone()).await.unwrap();
        assert_eq!(
            db.recent_project_workspaces(fs.as_ref())
                .await
                .unwrap()
                .len(),
            0
        );
        db.garbage_collect_workspaces(fs.as_ref(), "current", Some("previous"))
            .await
            .unwrap();
        assert_eq!(db.workspace_for_id(WorkspaceId(1)), Some(saved));
        assert!(db.workspace_for_id(WorkspaceId(2)).is_some());
        db.garbage_collect_workspaces(fs.as_ref(), "current", None)
            .await
            .unwrap();
        assert!(db.workspace_for_id(WorkspaceId(2)).is_none());
        assert!(
            db.claim_workspace(
                WorkspaceId(1),
                (Some("current".to_owned()), Some(1), None),
                (Some("next".to_owned()), Some(3), None),
                None,
            )
            .await
            .unwrap()
        );
        assert_eq!(
            db.recent_project_workspaces(fs.as_ref())
                .await
                .unwrap()
                .into_iter()
                .map(|workspace| workspace.workspace_id)
                .collect::<Vec<_>>(),
            vec![WorkspaceId(1)]
        );
    }

    #[gpui::test]
    async fn test_restore_window_with_linked_worktree_and_multiple_project_groups(
        cx: &mut gpui::TestAppContext,
    ) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());

        // Main git repo at /repo
        fs.insert_tree(
            "/repo",
            json!({
                ".git": {
                    "HEAD": "ref: refs/heads/main",
                    "worktrees": {
                        "feature": {
                            "commondir": "../../",
                            "HEAD": "ref: refs/heads/feature"
                        }
                    }
                },
                "src": { "main.rs": "" }
            }),
        )
        .await;

        // Linked worktree checkout pointing back to /repo
        fs.insert_tree(
            "/worktree-feature",
            json!({
                ".git": "gitdir: /repo/.git/worktrees/feature",
                "src": { "lib.rs": "" }
            }),
        )
        .await;

        // --- Phase 1: Set up the original multi-workspace window ---

        let project_1 = Project::test(fs.clone(), ["/repo".as_ref()], cx).await;
        let project_1_linked_worktree =
            Project::test(fs.clone(), ["/worktree-feature".as_ref()], cx).await;

        // Wait for git discovery to finish.
        cx.run_until_parked();

        // Create a second, unrelated project so we have two distinct project groups.
        fs.insert_tree(
            "/other-project",
            json!({
                ".git": { "HEAD": "ref: refs/heads/main" },
                "readme.md": ""
            }),
        )
        .await;
        let project_2 = Project::test(fs.clone(), ["/other-project".as_ref()], cx).await;
        cx.run_until_parked();

        // Create the MultiWorkspace with project_2, then add the main repo
        // and its linked worktree. The linked worktree is added last and
        // becomes the active workspace.
        let (multi_workspace, cx) = cx
            .add_window_view(|window, cx| MultiWorkspace::test_new(project_2.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| {
            mw.open_sidebar(cx);
        });

        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.test_add_workspace(project_1.clone(), window, cx);
        });

        let workspace_worktree = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.test_add_workspace(project_1_linked_worktree.clone(), window, cx)
        });

        let tasks =
            multi_workspace.update_in(cx, |mw, window, cx| mw.flush_all_serialization(window, cx));
        cx.run_until_parked();
        for task in tasks {
            task.await;
        }
        cx.run_until_parked();

        let active_db_id = workspace_worktree.read_with(cx, |ws, _| ws.database_id());
        assert!(
            active_db_id.is_some(),
            "Active workspace should have a database ID"
        );

        // --- Phase 2: Read back and verify the serialized state ---

        let session_id = multi_workspace
            .read_with(cx, |mw, cx| mw.workspace().read(cx).session_id())
            .unwrap();
        let db = cx.update(|_, cx| WorkspaceDb::global(cx));
        let session_workspaces = db
            .last_session_workspace_locations(&session_id, None, fs.as_ref())
            .await
            .expect("should load session workspaces");
        assert!(
            !session_workspaces.is_empty(),
            "Should have at least one session workspace"
        );

        let multi_workspaces =
            cx.update(|_, cx| read_serialized_multi_workspaces(session_workspaces, cx));
        assert_eq!(
            multi_workspaces.len(),
            1,
            "All workspaces share one window, so there should be exactly one multi-workspace"
        );

        let serialized = &multi_workspaces[0];
        assert_eq!(
            serialized.active_workspace.workspace_id,
            active_db_id.unwrap(),
        );
        assert_eq!(serialized.state.project_groups.len(), 2,);

        // Verify the serialized project group keys round-trip back to the
        // originals.
        let restored_keys: Vec<ProjectGroupKey> = serialized
            .state
            .project_groups
            .iter()
            .cloned()
            .map(Into::into)
            .collect();
        let expected_keys = vec![
            ProjectGroupKey::new(None, PathList::new(&["/repo"])),
            ProjectGroupKey::new(None, PathList::new(&["/other-project"])),
        ];
        assert_eq!(
            restored_keys, expected_keys,
            "Deserialized project group keys should match the originals"
        );

        // --- Phase 3: Restore the window and verify the result ---

        let app_state =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).app_state().clone());

        let serialized_mw = multi_workspaces.into_iter().next().unwrap();
        let restored_handle: gpui::WindowHandle<MultiWorkspace> = cx
            .update(|_, cx| {
                cx.spawn(async move |mut cx| {
                    crate::restore_multiworkspace(serialized_mw, app_state, &mut cx).await
                })
            })
            .await
            .expect("restore_multiworkspace should succeed");

        cx.run_until_parked();

        // The restored window should have the same project group keys.
        let restored_keys: Vec<ProjectGroupKey> = restored_handle
            .read_with(cx, |mw: &MultiWorkspace, _cx| mw.project_group_keys())
            .unwrap();
        assert_eq!(
            restored_keys, expected_keys,
            "Restored window should have the same project group keys as the original"
        );

        // The active workspace in the restored window should have the linked
        // worktree paths.
        let active_paths: Vec<PathBuf> = restored_handle
            .read_with(cx, |mw: &MultiWorkspace, cx| {
                mw.workspace()
                    .read(cx)
                    .root_paths(cx)
                    .into_iter()
                    .map(|p: Arc<Path>| p.to_path_buf())
                    .collect()
            })
            .unwrap();
        assert_eq!(
            active_paths,
            vec![PathBuf::from("/worktree-feature")],
            "The restored active workspace should be the linked worktree project"
        );

        let repo_key = ProjectGroupKey::new(None, PathList::new(&["/repo"]));
        let other_key = ProjectGroupKey::new(None, PathList::new(&["/other-project"]));
        let linked_key = ProjectGroupKey::new(None, PathList::new(&["/worktree-feature"]));
        multi_workspace
            .update_in(cx, |multi_workspace, window, cx| {
                multi_workspace.remove_project_group(&other_key, window, cx)
            })
            .await
            .unwrap();
        multi_workspace.update(cx, |multi_workspace, cx| {
            multi_workspace.restore_project_groups(
                vec![crate::SerializedProjectGroupState {
                    key: linked_key.clone(),
                    expanded: true,
                }],
                cx,
            );
            multi_workspace.set_all_groups_expanded(false);
            multi_workspace.normalize_project_groups(
                &[
                    (linked_key, repo_key.clone()),
                    (other_key.clone(), other_key),
                ],
                cx,
            );
            assert_eq!(
                multi_workspace
                    .project_groups(cx)
                    .into_iter()
                    .map(|group| (group.key, group.expanded))
                    .collect::<Vec<_>>(),
                vec![(repo_key, false)]
            );
        });
    }

    #[gpui::test]
    async fn test_remove_project_group_falls_back_to_neighbor(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let dir_a = unique_test_dir(&fs, "group-a").await;
        let dir_b = unique_test_dir(&fs, "group-b").await;
        let dir_c = unique_test_dir(&fs, "group-c").await;

        let project_a = Project::test(fs.clone(), [dir_a.as_path()], cx).await;
        let project_b = Project::test(fs.clone(), [dir_b.as_path()], cx).await;
        let project_c = Project::test(fs.clone(), [dir_c.as_path()], cx).await;

        // Create a multi-workspace with project A, then add B and C.
        // project_groups stores newest first: [C, B, A].
        // Sidebar displays in the same order: C (top), B (middle), A (bottom).
        let (multi_workspace, cx) = cx
            .add_window_view(|window, cx| MultiWorkspace::test_new(project_a.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| mw.open_sidebar(cx));

        let workspace_b = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.test_add_workspace(project_b.clone(), window, cx)
        });
        let _workspace_c = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.test_add_workspace(project_c.clone(), window, cx)
        });
        cx.run_until_parked();

        let key_a = project_a.read_with(cx, |p, cx| p.project_group_key(cx));
        let key_b = project_b.read_with(cx, |p, cx| p.project_group_key(cx));
        let key_c = project_c.read_with(cx, |p, cx| p.project_group_key(cx));

        // Activate workspace B so removing its group exercises the fallback.
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.activate(workspace_b.clone(), None, window, cx);
        });
        cx.run_until_parked();

        // --- Remove group B (the middle one). ---
        // In the sidebar [C, B, A], "below" B is A.
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.remove_project_group(&key_b, window, cx)
                .detach_and_log_err(cx);
        });
        cx.run_until_parked();

        let active_paths =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).root_paths(cx));
        assert_eq!(
            active_paths
                .iter()
                .map(|p| p.to_path_buf())
                .collect::<Vec<_>>(),
            vec![dir_a.clone()],
            "After removing the middle group, should fall back to the group below (A)"
        );

        // After removing B, keys = [A, C], sidebar = [C, A].
        // Activate workspace A (the bottom) so removing it tests the
        // "fall back upward" path.
        let workspace_a =
            multi_workspace.read_with(cx, |mw, _cx| mw.workspaces().next().unwrap().clone());
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.activate(workspace_a.clone(), None, window, cx);
        });
        cx.run_until_parked();

        // --- Remove group A (the bottom one in sidebar). ---
        // Nothing below A, so should fall back upward to C.
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.remove_project_group(&key_a, window, cx)
                .detach_and_log_err(cx);
        });
        cx.run_until_parked();

        let active_paths =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).root_paths(cx));
        assert_eq!(
            active_paths
                .iter()
                .map(|p| p.to_path_buf())
                .collect::<Vec<_>>(),
            vec![dir_c.clone()],
            "After removing the bottom group, should fall back to the group above (C)"
        );

        // --- Remove group C (the only one remaining). ---
        // Should create an empty workspace.
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.remove_project_group(&key_c, window, cx)
                .detach_and_log_err(cx);
        });
        cx.run_until_parked();

        let active_paths =
            multi_workspace.read_with(cx, |mw, cx| mw.workspace().read(cx).root_paths(cx));
        assert!(
            active_paths.is_empty(),
            "After removing the only remaining group, should have an empty workspace"
        );
    }

    /// Regression test for a crash where `find_or_create_local_workspace`
    /// returned a workspace that was about to be removed, hitting an assert
    /// in `MultiWorkspace::remove`.
    ///
    /// The scenario: two workspaces share the same root paths (e.g. due to
    /// a provisional key mismatch). When the first is removed and the
    /// fallback searches for the same paths, `workspace_for_paths` must
    /// skip the doomed workspace so the assert in `remove` is satisfied.
    #[gpui::test]
    async fn test_remove_fallback_skips_excluded_workspaces(cx: &mut gpui::TestAppContext) {
        crate::tests::init_test(cx);

        let fs = fs::FakeFs::new(cx.executor());
        let dir = unique_test_dir(&fs, "shared").await;

        // Two projects that open the same directory — this creates two
        // workspaces whose root_paths are identical.
        let project_a = Project::test(fs.clone(), [dir.as_path()], cx).await;
        let project_b = Project::test(fs.clone(), [dir.as_path()], cx).await;

        let (multi_workspace, cx) = cx
            .add_window_view(|window, cx| MultiWorkspace::test_new(project_a.clone(), window, cx));

        multi_workspace.update(cx, |mw, cx| mw.open_sidebar(cx));

        let workspace_b = multi_workspace.update_in(cx, |mw, window, cx| {
            mw.test_add_workspace(project_b.clone(), window, cx)
        });
        cx.run_until_parked();

        // workspace_a is first in the workspaces vec.
        let workspace_a =
            multi_workspace.read_with(cx, |mw, _| mw.workspaces().next().cloned().unwrap());
        assert_ne!(workspace_a, workspace_b);

        // Activate workspace_a so removing it triggers the fallback path.
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.activate(workspace_a.clone(), None, window, cx);
        });
        cx.run_until_parked();

        // Remove workspace_a. Its replacement is looked up by the same paths,
        // so workspace_a itself has to be skipped or it would be picked again.
        multi_workspace.update_in(cx, |mw, window, cx| {
            mw.remove(
                vec![workspace_a.clone()],
                RemovalIntent::CloseProject,
                window,
                cx,
            )
            .detach_and_log_err(cx);
        });
        cx.run_until_parked();

        // workspace_b should now be active — workspace_a was removed.
        multi_workspace.read_with(cx, |mw, _cx| {
            assert_eq!(
                mw.workspace(),
                &workspace_b,
                "fallback should have found workspace_b, not the excluded workspace_a"
            );
        });
    }

    struct PendingRestoration {
        resume: Shared<oneshot::Receiver<()>>,
        blocked_item_id: ItemId,
        runtime_ids: [ItemId; 2],
        items: HashMap<ItemId, gpui::Entity<TestItem>>,
    }

    impl Global for PendingRestoration {}

    fn persisted_test_item(
        workspace_id: WorkspaceId,
        contents: String,
        cx: &mut gpui::Context<TestItem>,
    ) -> TestItem {
        let key = format!("{workspace_id:?}/{}", cx.entity_id().as_u64());
        let mut item = TestItem::new_deserialized(workspace_id, cx)
            .with_dirty(true)
            .with_serialize({
                let contents = contents.clone();
                move || {
                    let key = key.clone();
                    let contents = contents.clone();
                    Some(Box::pin(async move {
                        Ok(KeyValueStore::prepare_write_kvp(key, contents))
                    }))
                }
            });
        item.state = contents;
        item
    }

    fn restoration_payloads(
        kvp: &KeyValueStore,
        workspace_id: WorkspaceId,
        item_ids: [ItemId; 2],
    ) -> [String; 2] {
        item_ids.map(|item_id| {
            kvp.read_kvp(&format!("{workspace_id:?}/{item_id}"))
                .unwrap()
                .unwrap()
        })
    }
}
