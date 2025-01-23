use std::collections::{HashSet, HashMap};
use crate::page::{Page, PageId};
use crate::value::Value;
use crate::storage::StorageManager;
use crate::path::Path;
use crate::page_manager::PageManager;

pub struct Batch<'a, V: Value> {
    committed: bool,
    // root_page: SubtriePage<'a>,
    updated: HashMap<Path, V>,
    deleted: HashSet<Path>,
    dirty_pages: Vec<(PageId, Page<'a>)>,
    orphaned_pages: Vec<PageId>,
}

impl<'a, V: Value> Batch<'a, V> {
    pub fn new() -> Self {
        Self { 
            committed: false,
            // root_page: SubtriePage::from_id_and_page(0, Page::default()),
            updated: HashMap::new(),
            deleted: HashSet::new(),
            dirty_pages: Vec::new(),
            orphaned_pages: Vec::new(),
        }
    }

    pub fn is_committed(&self) -> bool {
        self.committed
    }

    pub fn get(&self, key: Path) -> Option<V> {
        todo!()
    }

    pub fn insert(&mut self, key: Path, value: V) {
        if self.committed {
            panic!("Cannot insert into a committed batch");
        }
        if self.deleted.contains(&key) {
            self.deleted.remove(&key);
        }
        if self.updated.contains_key(&key) {
            self.updated.remove(&key);
        }
        self.updated.insert(key, value);
        // maybe start applying the update in the background
    }

    pub fn delete(&mut self, key: Path) {
        if self.committed {
            panic!("Cannot delete from a committed batch");
        }
        if self.updated.contains_key(&key) {
            self.updated.remove(&key);
        }
        if self.deleted.contains(&key) {
            self.deleted.remove(&key);
        }
        self.deleted.insert(key);
        // maybe start applying the delete in the background
    }

    pub fn commit<P: PageManager>(&mut self, storage_manager: &mut StorageManager<P>) {
        if self.committed {
            panic!("Cannot commit a committed batch");
        }
        // todo: optimize this by applying updates and deletes in parallel
        self.apply_updates(storage_manager);
        self.apply_deletes(storage_manager);

        // todo: ordering matters, as pages depend on each other
        // for (page_id, page) in self.dirty_pages {
        //     storage_manager.commit_page(page_id, page);
        // }
        self.committed = true;
    }

    fn apply_updates<P: PageManager>(&mut self, storage_manager: &mut StorageManager<P>) {
        for (key, value) in self.updated.iter() {
            storage_manager.insert(key.clone(), value.clone());
        }
    }

    fn apply_deletes<P: PageManager>(&mut self, storage_manager: &mut StorageManager<P>) {
        for key in self.deleted.iter() {
            storage_manager.delete(key.clone());
        }
    }
}

