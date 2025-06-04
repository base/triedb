use std::fmt::Debug;

#[derive(Default)]
pub struct DebugPage {
    pub nodes_per_page: DebugStats,
    pub bytes_per_page: DebugStats,
    pub depth_of_trie_in_nodes: DebugStats,
    pub depth_of_trie_in_pages: DebugStats,
    pub path_prefix_length: DebugStats,
    pub num_children_per_branch: DebugStats,
    pub node_size_in_bytes: DebugStats,
}

impl Debug for DebugPage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\nNodes Per Page: {:?}\nBytes Per Page: {:?}\nDepth of Trie in Nodes: {:?}\nDepth of Trie in Pages: {:?}\nPath Prefix Length: {:?}\nNum Children Per Branch: {:?}\nNode Size in Bytes: {:?}", self.nodes_per_page, self.bytes_per_page, self.depth_of_trie_in_nodes, self.depth_of_trie_in_pages, self.path_prefix_length, self.num_children_per_branch, self.node_size_in_bytes)
    }
}

pub struct DebugStats {
    min: usize,
    max: usize,
    total_sum: usize,
    count: usize,
}

impl DebugStats {
    pub fn update_stats(&mut self, new_val: usize) {
        if new_val > self.max {
            self.max = new_val;
        }
        if new_val < self.min {
            self.min = new_val;
        }
        self.total_sum += new_val;
        self.count += 1;
    }
}

impl Default for DebugStats {
    fn default() -> Self {
        Self { min: usize::MAX, max: usize::MIN, total_sum: 0, count: 0 }
    }
}

impl Debug for DebugStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "min: {}, max: {}, total sum: {}, count: {}, mean: {}",
            self.min,
            self.max,
            self.total_sum,
            self.count,
            self.total_sum as f64 / self.count as f64
        )
    }
}
