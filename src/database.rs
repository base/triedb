use crate::page::MmapPageManager;
use crate::page::OrphanPageManager;
use crate::page::PageError;
use crate::page::PageId;
use crate::page::PageKind;
use crate::page::PageManager;
use crate::page::RootPage;
use crate::snapshot::SnapshotId;
use crate::storage::engine;
use crate::storage::engine::StorageEngine;
use crate::transaction::Transaction;
use crate::transaction::TransactionManager;
use crate::transaction::{RO, RW};
use alloy_primitives::B256;
use alloy_trie::EMPTY_ROOT_HASH;
use std::sync::Arc;
use std::sync::RwLock;

#[derive(Debug, Clone)]
pub struct Database<P: PageManager> {
    pub(crate) inner: Arc<Inner<P>>,
}

#[derive(Debug)]
pub(crate) struct Inner<P: PageManager> {
    pub(crate) metadata: RwLock<Metadata>,
    pub(crate) storage_engine: RwLock<StorageEngine<P>>,
    pub(crate) transaction_manager: RwLock<TransactionManager>,
}

#[derive(Debug, Clone)]
pub struct Metadata {
    pub(crate) root_page_id: PageId,
    pub(crate) root_subtrie_page_id: PageId,
    pub(crate) max_page_number: PageId,
    pub(crate) snapshot_id: SnapshotId,
    pub(crate) state_root: B256,
}

impl Metadata {
    pub fn next(&self) -> Self {
        Self {
            snapshot_id: self.snapshot_id + 1,
            root_page_id: (self.root_page_id + 1) % 2,
            max_page_number: self.max_page_number,
            root_subtrie_page_id: self.root_subtrie_page_id,
            state_root: self.state_root,
        }
    }
}

#[derive(Debug)]
pub struct TransactionContext {
    pub(crate) metadata: Metadata,
    // TODO: add others for transaction context like metrics, etc.
}

impl TransactionContext {
    pub fn new(metadata: Metadata) -> Self {
        Self { metadata }
    }
}

#[derive(Debug)]
pub enum Error {
    PageError(PageError),
    CloseError(engine::Error),
}

impl Database<MmapPageManager> {
    pub fn create(file_path: &str) -> Result<Self, Error> {
        // TODO: handle the case where the file already exists.
        let mut page_manager = MmapPageManager::open(file_path).map_err(Error::PageError)?;
        // allocate the first 256 pages for the root, orphans, and root subtrie
        page_manager.resize(3_000_000).map_err(Error::PageError)?;
        for i in 0..256 {
            let page = page_manager.allocate(0).map_err(Error::PageError)?;
            assert_eq!(page.page_id(), i);
        }

        let orphan_manager = OrphanPageManager::new();

        let _root0 = page_manager.allocate(0).map_err(Error::PageError)?;
        let _root1 = page_manager.allocate(0).map_err(Error::PageError)?;
        let _subtrie = page_manager.allocate(0).map_err(Error::PageError)?;

        let metadata = Metadata {
            snapshot_id: 0,
            root_page_id: 0,
            max_page_number: 256,
            root_subtrie_page_id: 256,
            state_root: EMPTY_ROOT_HASH,
        };

        let db = Self::new(metadata, StorageEngine::new(page_manager, orphan_manager));

        let tx = db.begin_rw().unwrap();
        tx.commit().unwrap();

        Ok(db)
    }

    pub fn open(file_path: &str) -> Result<Self, Error> {
        let page_manager = MmapPageManager::open(file_path).map_err(Error::PageError)?;

        let root_page_0 = page_manager.get(0, 0).map_err(Error::PageError)?;
        let root_page_1 = page_manager.get(0, 1).map_err(Error::PageError)?;

        let root_0 = RootPage::try_from(root_page_0).map_err(Error::PageError)?;
        let root_1 = RootPage::try_from(root_page_1).map_err(Error::PageError)?;

        let root_page = if root_0.snapshot_id() > root_1.snapshot_id() {
            root_0
        } else {
            root_1
        };

        let max_page_count = root_page.max_page_number();

        let orphaned_page_ids = root_page
            .get_orphaned_page_ids(&page_manager)
            .map_err(Error::PageError)?;
        let orphan_manager = OrphanPageManager::new_with_unlocked_page_ids(orphaned_page_ids);

        let metadata: Metadata = root_page.into();

        let storage_engine = StorageEngine::new(page_manager, orphan_manager);
        let database = Database::new(metadata, storage_engine);
        // add a buffer of 20 pages
        database.resize(max_page_count + 20).unwrap();
        Ok(database)
    }
}

impl<P: PageManager> Drop for Database<P> {
    fn drop(&mut self) {
        if let Err(e) = self.close() {
            if let Error::CloseError(engine::Error::EngineClosed) = e {
                return;
            }
            panic!("Failed to close database: {:?}", e);
        }
    }
}

impl<P: PageManager> Database<P> {
    pub fn new(metadata: Metadata, storage_engine: StorageEngine<P>) -> Self {
        Self {
            inner: Arc::new(Inner {
                metadata: RwLock::new(metadata),
                storage_engine: RwLock::new(storage_engine),
                transaction_manager: RwLock::new(TransactionManager::new()),
            }),
        }
    }

    pub fn begin_rw(&self) -> Result<Transaction<'_, RW, P>, ()> {
        let mut transaction_manager = self.inner.transaction_manager.write().unwrap();
        let storage_engine = self.inner.storage_engine.read().unwrap();
        let metadata = self.inner.metadata.read().unwrap().next();
        let min_snapshot_id = transaction_manager.begin_rw(metadata.snapshot_id)?;
        storage_engine.unlock(min_snapshot_id - 1);
        let context = TransactionContext::new(metadata);
        Ok(Transaction::new(context, self, None))
    }

    pub fn begin_ro(&self) -> Result<Transaction<'_, RO, P>, ()> {
        let mut transaction_manager = self.inner.transaction_manager.write().unwrap();
        let storage_engine = self.inner.storage_engine.read().unwrap();
        let metadata = self.inner.metadata.read().unwrap().clone();
        transaction_manager.begin_ro(metadata.snapshot_id)?;
        let context = TransactionContext::new(metadata);
        Ok(Transaction::new(context, self, Some(storage_engine)))
    }

    pub(crate) fn resize(&self, new_page_count: PageId) -> Result<(), ()> {
        let mut storage_engine = self.inner.storage_engine.write().unwrap();
        storage_engine.resize(new_page_count).unwrap();
        Ok(())
    }

    pub fn close(&mut self) -> Result<(), Error> {
        let metadata = self.inner.metadata.read().unwrap();
        let context = TransactionContext::new(metadata.clone());
        let storage_engine = self.inner.storage_engine.read().unwrap();
        storage_engine.close(&context).map_err(Error::CloseError)?;
        Ok(())
    }

    pub fn size(&self) -> u32 {
        let storage_engine = self.inner.storage_engine.read().unwrap();
        storage_engine.size()
    }
}

impl<'p, P: PageKind> From<RootPage<'p, P>> for Metadata {
    fn from(root_page: RootPage<'p, P>) -> Self {
        Self {
            root_page_id: root_page.page_id(),
            root_subtrie_page_id: root_page.root_subtrie_page_id(),
            max_page_number: root_page.max_page_number(),
            snapshot_id: root_page.snapshot_id(),
            state_root: root_page.state_root(),
        }
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::{address, B256, U256};
    use std::fs::File;
    use tempdir::TempDir;

    use crate::{account::AccountVec, path::AddressPath};

    use super::*;

    #[test]
    fn test_set_get_account() {
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db").to_str().unwrap().to_owned();
        let db = Database::create(file_path.as_str()).unwrap();

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");

        let account1 = AccountVec::new(U256::from(100), 1, B256::ZERO, B256::ZERO);
        let mut tx = db.begin_rw().unwrap();
        tx.set_account(AddressPath::for_address(address), Some(account1.clone()))
            .unwrap();

        tx.commit().unwrap();

        let account2 = AccountVec::new(U256::from(123), 456, B256::ZERO, B256::ZERO);
        let mut tx = db.begin_rw().unwrap();
        tx.set_account(AddressPath::for_address(address), Some(account2.clone()))
            .unwrap();

        let ro_tx = db.begin_ro().unwrap();
        tx.commit().unwrap();

        // The read transaction was created before the write was committed, so it should not see the changes.
        let read_account = ro_tx
            .get_account(AddressPath::for_address(address))
            .unwrap();

        assert_eq!(account1, read_account.unwrap());

        // The writer transaction is committed, so the read transaction should see the changes.
        let ro_tx = db.begin_ro().unwrap();

        let read_account = ro_tx
            .get_account(AddressPath::for_address(address))
            .unwrap();

        assert_eq!(account2, read_account.unwrap());

        // cleanup
        tmp_dir.close().unwrap();
    }

    #[test]
    fn test_open_resize() {
        // GIVEN: a database
        //
        // create the database on disk. currently this
        // will create a database with N pages (see 'create' for N).
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db").to_str().unwrap().to_owned();
        let _db = Database::create(file_path.as_str()).unwrap();

        // WHEN: the database is opened
        let db = Database::open(file_path.as_str()).unwrap();

        // THEN: the size of the database should be the
        // max_page_size + buffer
        let open_size = db.size();

        let max_page_size = 256; // fresh db has root pages + reserved orphan pages
        assert_eq!(open_size, max_page_size + 20);

        // cleanup
        tmp_dir.close().unwrap();
    }

    #[test]
    fn test_close_resize() {
        // GIVEN: a database
        //
        // create the database on disk. currently this
        // will create a database with N pages (see 'create' for N).
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db").to_str().unwrap().to_owned();
        let mut db = Database::create(file_path.as_str()).unwrap();
        let create_size = db.size();

        assert_eq!(create_size, 3000000);

        // WHEN: the database is closed
        db.close().unwrap();

        // THEN: the size of the database should be the
        // max_page_size
        let max_page_size = 256; // fresh db so at least 256 pages for the root pages + orphan pages
        let file = File::options().read(true).open(file_path.as_str()).unwrap();
        let file_len = file.metadata().unwrap().len();
        assert_eq!(file_len, max_page_size * 4096);

        // cleanup
        tmp_dir.close().unwrap();
    }

    #[test]
    fn test_auto_close_database() {
        // GIVEN: a database
        //
        // create the database on disk. currently this
        // will create a database with N pages (see 'create' for N).
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db").to_str().unwrap().to_owned();

        {
            let db = Database::create(file_path.as_str()).unwrap();

            let create_size = db.size();
            assert_eq!(create_size, 3_000_000);
        }

        // WHEN: the database is dropped from scope
        // THEN: the database should be closed and the file should be truncated
        let max_page_size = 256; // fresh db so at least 256 pages for the root pages + orphan pages
        let file = File::options().read(true).open(file_path.as_str()).unwrap();
        let file_len = file.metadata().unwrap().len();
        assert_eq!(file_len, max_page_size * 4096);

        // cleanup
        tmp_dir.close().unwrap();
    }
}
