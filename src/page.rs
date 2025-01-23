use crate::nodes::TrieNode;
use crate::nodes::reference::NodeReference;
use crate::value::Value;

pub const PAGE_SIZE: usize = 4096;

#[derive(Debug, PartialEq, Eq)]
pub struct Page<'a> {
    data: &'a mut [u8; PAGE_SIZE],
}

// impl<'a> Default for Page<'a> {
//     fn default() -> Self {
//         Self { data: RefCell::new([0u8; PAGE_SIZE as usize]) }
//     }
// }

impl<'a> Page<'a> {
    pub fn new(data: &'a mut [u8; PAGE_SIZE]) -> Self {
        Self { data }
    }

    pub fn from_slice(slice: &'a mut [u8]) -> Self {
        Self::new(slice.try_into().expect("Invalid slice length"))
    }

    // pub fn as_bytes(self) -> [u8; PAGE_SIZE as usize] {
    //     *self.data
    // }
}

pub type PageId = u32;

pub type IdentifiedPage<'a> = (PageId, Page<'a>);

#[derive(Debug, PartialEq, Eq)]
pub struct SubtriePage<'a> {
    pub page_id: PageId,
    page: Page<'a>,
    // TODO: include lazily-cached versions of the raw nodes
}

impl<'a> SubtriePage<'a> {
    pub fn from_id_and_page(id: PageId, page: Page<'a>) -> Self {
        Self {
            page_id: id,
            page,
        }
    }

    pub fn from_identified_page(identified_page: IdentifiedPage<'a>) -> Self {
        Self::from_id_and_page(identified_page.0, identified_page.1)
    }

    pub fn as_identified_page(self) -> IdentifiedPage<'a> {
        (self.page_id, self.page)
    }

    pub fn inspect(&self) {
        println!("Page ID: {:?}", self.page_id);
        println!("Dirty: {:?}", self.is_dirty());
        // println!("Page: {:?}", self.page.borrow().data);
        println!("Node count: {:?}", self.node_count());
        for (i, ptr) in self.ptrs_iter().enumerate() {
            println!("Node pointer {}: {:?}", i, ptr);
        }
        for (i, ptr) in self.ptrs_iter().enumerate() {
            if ptr.is_removed() {
                continue;
            }
            println!("Node {}: {:?}", i, self.get_node::<String>(i as u8));
        }
    }

    pub fn is_dirty(&self) -> bool {
        self.page.data[0] == 1
    }

    pub fn set_dirty(&mut self, dirty: bool) {
        self.page.data[0] = if dirty { 1 } else { 0 };
    }

    fn set_node_count(&mut self, count: u8) {
        self.page.data[1] = count;
    }

    fn node_count(&self) -> u8 {
        self.page.data[1]
    }

    fn set_ptr(&mut self, index: u8, ptr: NodePointer) {
        let start_index = (16 + index * 4) as usize;
        let end_index = start_index + 4;
        self.page.data[start_index..end_index].copy_from_slice(&ptr.as_bytes());
    }

    fn get_ptr(&self, index: u8) -> Option<NodePointer> {
        let start_index = (16 + index * 4) as usize;
        let end_index = start_index + 4;
        Some(NodePointer::from_bytes(&self.page.data[start_index..end_index]))
    }

    fn ptrs_iter(&self) -> impl Iterator<Item = NodePointer> + '_ {
        (0..self.node_count())
            .filter_map(|i| self.get_ptr(i as u8))
    }

    pub fn get_node<V: Value>(&self, index: u8) -> Option<TrieNode<V>> {
        if index >= self.node_count() {
            return None;
        }

        let ptr = self.get_ptr(index)?;
        let start_index = (4096 - ptr.offset_from_end) as usize;
        let end_index = start_index + ptr.size as usize;
        let node_bytes = self.page.data[start_index..end_index].to_vec();
        Some(TrieNode::from_bytes(&node_bytes))
    }

    pub fn set_node<V: Value>(&mut self, index: u8, node: &TrieNode<V>) -> Option<NodeReference> {
        assert!(index < self.node_count(), "Index out of bounds");

        let mut ptr = self.get_ptr(index)?;
        let node_bytes = node.as_bytes();

        if node_bytes.len() > ptr.size as usize {
            return None;
        } else if node_bytes.len() < ptr.size as usize {
            ptr.size = node_bytes.len() as u16;
            self.set_ptr(index, ptr.clone());
        }

        let start_index = (4096 - ptr.offset_from_end) as usize;
        let end_index = start_index + ptr.size as usize;
        self.page.data[start_index..end_index].copy_from_slice(&node_bytes);
        self.set_dirty(true);
        Some(NodeReference::new_dirty(self.page_id, index as u8))
    }

    pub fn pop_node<V: Value>(&mut self, index: u8) -> Option<TrieNode<V>> {
        let ptr = self.get_ptr(index)?;
        if ptr.is_empty() {
            return None;
        }
        let node = self.get_node(index);
        self.set_ptr(index, ptr.removed());
        self.set_dirty(true);
        node
    }

    pub fn insert<V: Value>(&mut self, node: &TrieNode<V>) -> Option<NodeReference> {
        let size = node.encoded_size();
        let (index, pointer) = self.assign_pointer(size)?;
        self.set_node(index, node)
    }

    fn assign_pointer(&mut self, size: usize) -> Option<(u8, NodePointer)> {
        // TODO: handle fragmentation instead of only looking at the contiguous free space

        let free_space_start = self.free_space_start();
        let free_space_end = self.free_space_end();
        let free_space = free_space_end - free_space_start;
        if free_space < size {
            return None;
        }
        let index = self.node_count();
        // TODO: this is a hack to force nodes to spill over to the next page even with small numbers of nodes
        if index > 2 {
            return None;
        }
        self.set_node_count(index + 1);
        let offset = PAGE_SIZE - (free_space_end - size);
        let pointer = NodePointer { removed: false, offset_from_end: offset as u16, size: size as u16 };
        self.set_ptr(index, pointer.clone());
        self.set_dirty(true);
        Some((index, pointer))
    }

    fn free_space_start(&self) -> usize {
        self.header_size() + (self.node_count() * 4) as usize
    }

    fn free_space_end(&self) -> usize {
        PAGE_SIZE - self.ptrs_iter()
                .map(|ptr| ptr.offset_from_end as usize)
                .max()
                .unwrap_or(0)
    }

    fn header_size(&self) -> usize {
        16
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct NodePointer {
    removed: bool,
    offset_from_end: u16,
    size: u16,
}

impl NodePointer {
    pub fn is_empty(&self) -> bool {
        self.removed || self.size == 0
    }

    pub fn is_removed(&self) -> bool {
        self.removed
    }

    pub fn removed(self) -> Self {
        Self { removed: true, offset_from_end: self.offset_from_end, size: self.size }
    }

    pub fn as_bytes(&self) -> [u8; 4] {
        let mut data = [0u8; 4];
        data[0..2].copy_from_slice(&self.offset_from_end.to_le_bytes());
        data[2..].copy_from_slice(&self.size.to_le_bytes());
        if self.removed {
            data[1] |= 0x80;
        }
        data
    }

    pub fn from_bytes(data: &[u8]) -> Self {
        let offset = u16::from_le_bytes(data[0..2].try_into().expect("Invalid node pointer size")) & 0x7FFF;
        let size = u16::from_le_bytes(data[2..4].try_into().expect("Invalid node pointer size"));

        let removed = (data[1] & 0x80) != 0;

        Self {
            removed,
            offset_from_end: offset,
            size,
        }
    }
}
