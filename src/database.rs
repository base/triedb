use std::sync::Arc;
use std::sync::RwLock;
use crate::page::MmapPageManager;
use crate::page::OrphanPageManager;
use crate::page::PageError;
use crate::page::PageManager;
use crate::page::ReadablePage;
use crate::page::RootPage;
use crate::snapshot::SnapshotId;
use crate::storage::engine::StorageEngine;
use crate::transaction::TransactionManager;
use crate::transaction::{RW, RO};
use crate::transaction::Transaction;

#[derive(Debug)]
pub struct Database<P: PageManager> {
    pub(crate) inner: Arc<Inner<P>>,
}

#[derive(Debug)]
pub(crate) struct Inner<P: PageManager> {
    pub(crate) storage_engine: RwLock<StorageEngine<P>>,
    pub(crate) transaction_manager: RwLock<TransactionManager>,
}

#[derive(Debug)]
enum Error {
    PageError(PageError),
}

impl Database<MmapPageManager> {
    pub fn open(file_path: &str) -> Result<Self, Error> {
        let page_manager = MmapPageManager::open(file_path).map_err(Error::PageError)?;
        let orphan_manager = OrphanPageManager::new();

        // TODO: parse the root page to determine the correct metadata
        
        let root_page_0 = page_manager.get(0, 0).map_err(Error::PageError)?;
        let root_page_1 = page_manager.get(0, 1).map_err(Error::PageError)?;

        let root_0 = RootPage::try_from(root_page_0).map_err(Error::PageError)?;
        let root_1 = RootPage::try_from(root_page_1).map_err(Error::PageError)?;

        let root_page = if root_0.snapshot_id() > root_1.snapshot_id() {
            root_0
        } else {
            root_1
        };

        let storage_engine = StorageEngine::new(root_page.snapshot_id(), 0, root_page.page_id(), page_manager, orphan_manager);
        Ok(Database::new(storage_engine))
    }
}

impl<P: PageManager> Database<P> {
    pub fn new(storage_engine: StorageEngine<P>) -> Self {
        Self { inner: Arc::new(Inner { storage_engine: RwLock::new(storage_engine), transaction_manager: RwLock::new(TransactionManager::new()) }) }
    }

    pub fn begin_rw(&self) -> Result<Transaction<'_, RW, P>, ()> {
        let mut storage_engine = self.inner.storage_engine.write().unwrap();
        let mut transaction_manager = self.inner.transaction_manager.write().unwrap();
        let snapshot_id = storage_engine.snapshot_id() + 1;
        let min_snapshot_id = transaction_manager.begin_rw(snapshot_id)?;
        storage_engine.unlock(min_snapshot_id);
        Ok(Transaction::new(snapshot_id, self))
    }

    pub fn begin_ro(&self) -> Result<Transaction<'_, RO, P>, ()> {
        let storage_engine = self.inner.storage_engine.write().unwrap();
        let mut transaction_manager = self.inner.transaction_manager.write().unwrap();
        let snapshot_id = storage_engine.snapshot_id();
        transaction_manager.begin_ro(snapshot_id)?;
        Ok(Transaction::new(snapshot_id, self))
    }

    pub(crate) fn commit(&self, snapshot_id: SnapshotId) -> Result<(), ()> {
        let mut storage_engine = self.inner.storage_engine.write().unwrap();
        let mut transaction_manager = self.inner.transaction_manager.write().unwrap();
        storage_engine.commit(snapshot_id).unwrap();
        transaction_manager.remove_transaction(snapshot_id)?;
        Ok(())
    }

    pub(crate) fn rollback(&self, snapshot_id: SnapshotId) -> Result<(), ()> {
        let mut storage_engine = self.inner.storage_engine.write().unwrap();
        let mut transaction_manager = self.inner.transaction_manager.write().unwrap();
        storage_engine.rollback(snapshot_id).unwrap();
        transaction_manager.remove_transaction(snapshot_id)?;
        Ok(())
    }
}

