mod batch;
// mod database;
mod nodes;
mod page;
mod page_manager;
mod path;
mod storage;
mod value;

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {

    // pub struct DB {
    //     file: File,
    //     mmap: MmapMut,
    //     num_pages: usize,
    // }

    // impl DB {
    //     pub fn new(path: impl AsRef<Path>) -> std::io::Result<Self> {
    //         let file = OpenOptions::new().read(true).write(true).create(true).open(path)?;
    //         let mmap = unsafe { MmapMut::map_mut(&file)? };

    //         let num_pages = mmap.len() / 4096;
    //         Ok(Self { file, mmap, num_pages })
    //     }

    //     pub fn get_page(&mut self, page_id: usize) -> Option<Page> {
    //         if page_id >= self.num_pages {
    //             return None;
    //         }

    //         let start = page_id * 4096;
    //         let end = start + 4096;
    //         let slice = &mut self.mmap[start..end];
    //         let page = Page::from_slice(slice);
    //         Some(page)
    //     }

    //     pub fn allocate_page(&mut self) -> usize {
    //         let page_id = self.num_pages;
    //         self.num_pages += 1;

    //         self.ensure_capacity(page_id).unwrap();

    //         page_id
    //     }

    //     fn ensure_capacity(&mut self, page_id: usize) -> std::io::Result<()> {
    //         let required_size = (page_id + 1) * 4096;
    //         if self.mmap.len() < required_size {
    //             self.file.set_len(required_size as u64)?;
    //             self.mmap = unsafe { MmapMut::map_mut(&self.file)? };
    //         }
    //         Ok(())
    //     }

    //     pub fn commit_page(&mut self, page_id: usize) -> std::io::Result<()> {
    //         let start = page_id * 4096;
    //         self.mmap.flush_range(start, 4096)
    //     }
    // }

    // pub struct Page {
    //     data: Rc<RefCell<[u8; 4096]>>,
    // }

    // impl Page {
    //     pub fn from_slice(slice: &mut [u8]) -> Self {
    //         Self { data: Rc::new(RefCell::new(slice.try_into().expect("Invalid slice length"))) }
    //     }

    //     pub fn read(&self) -> &[u8; 4096] {
    //         &self.data
    //     }

    //     pub fn write(&mut self) -> &mut [u8; 4096] {
    //         &mut self.data
    //     }
    // }

    // #[test]
    // fn test_page_manager() {
    //     let mut db = DB::new("/tmp/test.db").unwrap();
    //     let page_id = db.allocate_page();
    //     let mut page = db.get_page(page_id).unwrap();
    //     let data = page.write();
    //     data[0] = 1;
    //     assert_eq!(page.read()[0], 1);
    //     assert_eq!(db.get_page(page_id).unwrap().read()[0], 1);
    //     db.commit_page(page_id).unwrap();
    //     assert_eq!(db.get_page(page_id).unwrap().read()[0], 1);
    //     db = DB::new("/tmp/test.db").unwrap();
    //     assert_eq!(db.get_page(page_id).unwrap().read()[0], 1);
    // }
}
