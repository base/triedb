use std::fmt::Debug;
use crate::page::{Page, PageId, PAGE_SIZE, IdentifiedPage};
use std::fs::File;
use std::fs::OpenOptions;
use memmap2::{MmapMut, MmapOptions};
use std::path::Path;
use std::sync::{Arc, RwLock};
pub trait PageManager: Debug {
    // TODO: separate between read-only and read-write page access
    fn get_page<'a>(&self, page_id: PageId) -> Option<Page<'a>>;
    fn resize(&mut self, page_id: PageId) -> std::io::Result<()>;
    fn allocate_page<'a>(&mut self) -> Result<IdentifiedPage<'a>, String>;
    fn commit_page(&mut self, page_id: PageId) -> Result<(), String>;
}

// #[derive(Debug)]
// pub struct InMemoryPageManager<'a> {
//     pages: HashMap<PageId, Page<'a>>,
// }

// impl<'a> InMemoryPageManager<'a> {
//     pub fn new() -> Self {
//         Self { pages: HashMap::new() }
//     }
// }

// impl<'a> PageManager for InMemoryPageManager<'a> {
//     fn get_page(&mut self, page_id: PageId) -> Option<Page<'a>> {
//         self.pages.get_mut(&page_id)
//     }

//     fn allocate_page(&mut self) -> IdentifiedPage {
//         let page_id = self.pages.len() as PageId;
//         let page = Rc::new(RefCell::new(Page::default()));
//         self.pages.insert(page_id, page.clone());
//         (page_id, page)
//     }

//     fn commit_page(&mut self, identified_page: IdentifiedPage) {
//         self.pages.insert(identified_page.0, identified_page.1);
//     }
// }

#[derive(Debug)]
pub struct MemoryMappedFilePageManager {
    file: Arc<RwLock<File>>,
    mmap: Arc<RwLock<MmapMut>>,
    next_page_id: PageId,
}

impl MemoryMappedFilePageManager {
    pub fn new(path: impl AsRef<Path>) -> std::io::Result<Self> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(path)?;
        
        // Ensure file is at least one page
        file.set_len((PAGE_SIZE * 1) as u64)?;
        
        let mmap = unsafe { MmapOptions::new().map_mut(&file)? };
        
        Ok(Self {
            file: Arc::new(RwLock::new(file)),
            mmap: Arc::new(RwLock::new(mmap)),
            next_page_id: 2, // Reserve 0 and 1 for roots
        })
    }
}

impl PageManager for MemoryMappedFilePageManager {
    fn get_page<'a>(&self, page_id: PageId) -> Option<Page<'a>> {
        let start = page_id as usize * PAGE_SIZE as usize;
        if start + PAGE_SIZE as usize <= self.mmap.read().unwrap().len() {
            let page_data = unsafe {
                &mut *(self.mmap.read().unwrap().as_ptr().add(start) as *mut [u8; PAGE_SIZE as usize])
            };
            Some(Page::from_slice(page_data))
        } else {
            None
        }
    }

    // WARNING: Resizing/remapping the file invalidates all existing mmap views!
    // This must not be called in the middle of a transaction!
    fn resize(&mut self, page_id: PageId) -> std::io::Result<()> {
        let file = self.file.write().unwrap();
        let mut mmap = self.mmap.write().unwrap();
        let required_len = (page_id as usize + 1) * PAGE_SIZE as usize;
        if required_len > mmap.len() {
            // Extend file
            file.set_len(required_len as u64)?;
            // Remap the file
            *mmap = unsafe { MmapOptions::new().map_mut(&*file)? };
        }
        Ok(())
    }

    fn allocate_page<'a>(&mut self) -> Result<IdentifiedPage<'a>, String> {
        let page_id = self.next_page_id;
        self.next_page_id += 1;
        
        let required_len = (page_id as usize + 1) * PAGE_SIZE as usize;
        let mut mmap = self.mmap.write().unwrap();
        if mmap.len() < required_len {
            return Err("Failed to allocate page: not enough space in mmap".to_string());
        }
        
        let start = page_id as usize * PAGE_SIZE as usize;

        let page_slice = &mut mmap[start..start + PAGE_SIZE as usize];
        
        // Initialize page with zeros
        page_slice.fill(0);

        let ptr = mmap.as_ptr();

        let page_data = unsafe {
            &mut *(ptr.add(start) as *mut [u8; PAGE_SIZE as usize])
        };
        let page = Page::new(page_data);
        
        Ok((page_id, page))
    }

    fn commit_page(&mut self, page_id: PageId) -> Result<(), String> {
        let start = page_id as usize * PAGE_SIZE as usize;
        self.mmap.write().unwrap().flush_range(start, PAGE_SIZE as usize).map_err(|e| format!("Failed to flush mmap: {}", e))?;
        Ok(())
    }
}
