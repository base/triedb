use parking_lot::Mutex;
use std::sync::Arc;
use triedb::{
    context::TransactionContext,
    storage::explorer::ExplorerService,
    Database,
};

/// Application state that holds the database and a read-only transaction context.
pub struct AppState {
    pub database: Arc<Database>,
    context: Mutex<TransactionContext>,
}

impl AppState {
    /// Creates a new AppState from a database path.
    pub fn new(db_path: &str) -> Result<Self, triedb::database::OpenError> {
        let database = Arc::new(Database::open(db_path)?);
        let context = database.read_context();
        Ok(Self {
            database,
            context: Mutex::new(context),
        })
    }

    /// Executes a function with an ExplorerService and TransactionContext.
    pub fn with_explorer<T, F>(&self, f: F) -> T
    where
        F: FnOnce(&ExplorerService<'_>, &TransactionContext) -> T,
    {
        let context = self.context.lock();
        let explorer = self.database.explorer();
        f(&explorer, &context)
    }
}
