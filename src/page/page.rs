mod page;

pub const PAGE_SIZE: usize = 4096;

#[derive(Debug, PartialEq, Eq)]
pub struct Page<'a> {
    data: &'a mut [u8; PAGE_SIZE],
}
