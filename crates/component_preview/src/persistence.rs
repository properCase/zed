use db::{
    query,
    sqlez::{domain::Domain, thread_safe_connection::ThreadSafeConnection},
    sqlez_macros::sql,
};
use workspace::{ItemId, WorkspaceDb, WorkspaceId};

pub struct ComponentPreviewDb(ThreadSafeConnection);

impl Domain for ComponentPreviewDb {
    const NAME: &str = stringify!(ComponentPreviewDb);

    const MIGRATIONS: &[&str] = &[sql!(
            CREATE TABLE component_previews (
                workspace_id INTEGER,
                item_id INTEGER UNIQUE,
                active_page_id TEXT,
                PRIMARY KEY(workspace_id, item_id),
                FOREIGN KEY(workspace_id) REFERENCES workspaces(workspace_id)
                ON DELETE CASCADE
            ) STRICT;
    )];
}

db::static_connection!(ComponentPreviewDb, [WorkspaceDb]);

impl ComponentPreviewDb {
    query! {
        pub fn prepare_save_active_page(
            item_id: ItemId,
            workspace_id: WorkspaceId,
            active_page_id: String,
        ) -> Write {
            INSERT INTO component_previews(item_id, workspace_id, active_page_id)
            VALUES (?1, ?2, ?3)
            ON CONFLICT DO UPDATE SET active_page_id = ?3
        }
    }

    query! {
        pub fn get_active_page(item_id: ItemId, workspace_id: WorkspaceId) -> Result<Option<String>> {
            SELECT active_page_id
            FROM component_previews
            WHERE item_id = ? AND workspace_id = ?
        }
    }
}
