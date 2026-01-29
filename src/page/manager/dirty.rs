use std::collections::{BTreeMap, HashSet};

use crate::page::PageId;

/// A container which tracks dirty pages in a memory mapped file.
#[derive(Debug, Default)]
pub(crate) struct DirtyPages {
    // A set of reallocated dirty pages which need to be flushed to disk.
    set: HashSet<PageId>,
    // Half-open ranges [start, end) of dirty pages, non-overlapping and non-adjacent.
    runs: BTreeMap<PageId, PageId>,
}

impl DirtyPages {
    /// Iterate over the dirty page runs as (byte offset, length) pairs.
    pub(crate) fn byte_runs<'a>(&'a self) -> impl Iterator<Item = (usize, usize)> + 'a {
        self.runs
            .iter()
            .map(|(&start, &end)| (start.as_offset(), end.as_offset() - start.as_offset()))
    }

    /// Marks a page as dirty, returning true if the page was newly marked.
    /// This attempts to find
    pub(crate) fn mark_dirty(&mut self, page_id: PageId) -> bool {
        if !self.set.insert(page_id) {
            return false;
        }

        let next_page_id = page_id.inc();

        // Find predecessor run: end <= id
        let predecessor = self.runs.range(..=page_id).next_back();
        let join_left = predecessor.is_some_and(|(_, &end)| end == page_id);

        // Find successor run: start > id
        let successor =
            next_page_id.and_then(|next_page_id| self.runs.range(next_page_id..).next());
        let join_right = successor.is_some_and(|(&start, _)| start == next_page_id.unwrap());

        match (join_left, join_right) {
            (true, true) => {
                // Join predecessor and successor runs into a single run
                let (&l_start, _) = predecessor.unwrap();
                let (&r_start, &r_end) = successor.unwrap();
                self.runs.remove(&l_start);
                self.runs.remove(&r_start);
                self.runs.insert(l_start, r_end);
            }
            (true, false) => {
                // Extend predecessor run to include id
                let (&l_start, _) = predecessor.unwrap();
                let l_end = self.runs.get_mut(&l_start).unwrap();
                *l_end = next_page_id.unwrap();
            }
            (false, true) => {
                // Extend successor run backwards to include id
                let (&r_start, &r_end) = successor.unwrap();
                self.runs.remove(&r_start);
                self.runs.insert(page_id, r_end);
            }
            (false, false) => {
                // Create new run containing only the id
                self.runs.insert(page_id, next_page_id.unwrap());
            }
        }

        true
    }

    /// Clears the dirty pages set and runs.
    pub(crate) fn clear(&mut self) {
        self.set.clear();
        self.runs.clear();
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use crate::page_id;

    use super::*;

    #[test]
    fn test_clear() {
        let mut dirty_pages = DirtyPages::default();
        assert!(dirty_pages.mark_dirty(page_id!(1)));
        assert!(!dirty_pages.mark_dirty(page_id!(1)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(0, 4096)]);

        dirty_pages.clear();
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![]);

        assert!(dirty_pages.mark_dirty(page_id!(1)));
        assert!(!dirty_pages.mark_dirty(page_id!(1)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(0, 4096)]);

        dirty_pages.clear();
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![]);
    }

    #[test]
    fn test_mark_dirty_noncontiguous_runs() {
        let mut dirty_pages = DirtyPages::default();

        assert!(dirty_pages.mark_dirty(page_id!(1)));
        assert!(!dirty_pages.mark_dirty(page_id!(1)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(0, 4096)]);

        assert!(dirty_pages.mark_dirty(page_id!(3)));
        assert!(!dirty_pages.mark_dirty(page_id!(3)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(0, 4096), (8192, 4096)]);

        assert!(dirty_pages.mark_dirty(page_id!(11)));
        assert_eq!(
            dirty_pages.byte_runs().collect::<Vec<_>>(),
            vec![(0, 4096), (8192, 4096), (40960, 4096)]
        );

        assert!(dirty_pages.mark_dirty(page_id!(101)));
        assert_eq!(
            dirty_pages.byte_runs().collect::<Vec<_>>(),
            vec![(0, 4096), (8192, 4096), (40960, 4096), (409600, 4096)]
        );

        dirty_pages.clear();
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![]);
    }

    #[test]
    fn test_mark_dirty_extend_right() {
        let mut dirty_pages = DirtyPages::default();

        assert!(dirty_pages.mark_dirty(page_id!(1)));
        assert!(!dirty_pages.mark_dirty(page_id!(1)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(0, 4096)]);

        assert!(dirty_pages.mark_dirty(page_id!(2)));
        assert!(!dirty_pages.mark_dirty(page_id!(2)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(0, 8192)]);

        assert!(dirty_pages.mark_dirty(page_id!(3)));
        assert!(!dirty_pages.mark_dirty(page_id!(3)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(0, 12288)]);

        assert!(dirty_pages.mark_dirty(page_id!(11)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(0, 12288), (40960, 4096)]);

        assert!(dirty_pages.mark_dirty(page_id!(12)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(0, 12288), (40960, 8192)]);

        dirty_pages.clear();
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![]);
    }

    #[test]
    fn test_mark_dirty_extend_left() {
        let mut dirty_pages = DirtyPages::default();

        assert!(dirty_pages.mark_dirty(page_id!(100)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(405504, 4096)]);

        assert!(dirty_pages.mark_dirty(page_id!(99)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(401408, 8192)]);

        assert!(dirty_pages.mark_dirty(page_id!(98)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(397312, 12288)]);

        assert!(dirty_pages.mark_dirty(page_id!(2)));
        assert_eq!(
            dirty_pages.byte_runs().collect::<Vec<_>>(),
            vec![(4096, 4096), (397312, 12288)]
        );

        assert!(dirty_pages.mark_dirty(page_id!(1)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(0, 8192), (397312, 12288)]);

        dirty_pages.clear();
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![]);
    }

    #[test]
    fn test_mark_dirty_extend_both() {
        let mut dirty_pages = DirtyPages::default();

        assert!(dirty_pages.mark_dirty(page_id!(100)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(405504, 4096)]);

        assert!(dirty_pages.mark_dirty(page_id!(99)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(401408, 8192)]);

        assert!(dirty_pages.mark_dirty(page_id!(101)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(401408, 12288)]);

        dirty_pages.clear();
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![]);
    }

    #[test]
    fn test_mark_dirty_merge_runs() {
        let mut dirty_pages = DirtyPages::default();

        assert!(dirty_pages.mark_dirty(page_id!(100)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(405504, 4096)]);

        assert!(dirty_pages.mark_dirty(page_id!(98)));
        assert_eq!(
            dirty_pages.byte_runs().collect::<Vec<_>>(),
            vec![(397312, 4096), (405504, 4096)]
        );

        assert!(dirty_pages.mark_dirty(page_id!(99)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(397312, 12288)]);

        assert!(dirty_pages.mark_dirty(page_id!(102)));
        assert_eq!(
            dirty_pages.byte_runs().collect::<Vec<_>>(),
            vec![(397312, 12288), (413696, 4096)]
        );

        assert!(dirty_pages.mark_dirty(page_id!(101)));
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![(397312, 20480)]);

        dirty_pages.clear();
        assert_eq!(dirty_pages.byte_runs().collect::<Vec<_>>(), vec![]);
    }

    proptest! {
        #[test]
        fn test_mark_dirty_random(page_ids in prop::collection::vec(any::<PageId>(), 1..1000)) {
            let mut dirty_pages = DirtyPages::default();
            for page_id in page_ids {
                dirty_pages.mark_dirty(page_id);
            }

            let runs = dirty_pages.byte_runs().collect::<Vec<_>>();
            assert!(runs.is_sorted_by_key(|(start, _)| *start));
            // ensure that runs are non-overlapping and non-adjacent
            assert!(runs.windows(2).all(|w| w[0].0 + w[0].1 < w[1].0));
        }
    }
}
