mod manager;
mod page;
mod slotted_page;

pub use manager::{mmap::PageManager, options::PageManagerOptions, PageError, PageId};
pub use page::{Page, PageMut};
pub use slotted_page::{SlottedPage, SlottedPageMut, CELL_POINTER_SIZE};
