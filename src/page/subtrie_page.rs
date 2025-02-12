use alloy_trie::Nibbles;

use crate::location::Location;

use super::{slotted_page::{SlottedStorage, Value}, PageError};

pub struct SubtriePage<'p, 'n, N: Node<'n>, S: SlottedStorage<'p, 'n, N>> {
    storage: S,
    _marker: std::marker::PhantomData<(&'p (), &'n (), N)>,
}

impl<'p, 'n, N: Node<'n>, S: SlottedStorage<'p, 'n, N>> SubtriePage<'p, 'n, N, S>
  where 'p: 'n, S::Error: Into<PageError> {
    pub fn root_node(&'n self) -> Result<N, PageError> {
        let val = self.storage.get_value(0);
        Ok(val.map_err(|e| e.into())?)
    }

    // Finds the next node in the path, returning the node and the remaining path.
    pub fn traverse_path(&'n self, index: u8, path: &Nibbles) -> Result<Option<(Location, Nibbles)>, PageError> {
        let node: N = self.storage.get_value(index).map_err(|e| e.into())?;
        let prefix = node.prefix();
        if path.eq(&prefix) {
            Ok(Some((Location::for_cell(index), Nibbles::new())))
        } else if path.starts_with(&prefix) {
            let remaining_path = path.slice(prefix.len()..);
            let child_index = path[prefix.len()];
            let maybe_child = node.child(child_index);
            if let Some(child) = maybe_child {
                Ok(Some((child, remaining_path)))
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }
}

impl<'p, 'n, N: Node<'n>, S: SlottedStorage<'p, 'n, N, Error = PageError>> From<S> for SubtriePage<'p, 'n, N, S> {
    fn from(storage: S) -> Self {
        Self { storage, _marker: std::marker::PhantomData }
    }
}

pub trait Node<'n>: Value<'n> {
    fn prefix(&self) -> Nibbles;
    fn child(&self, index: u8) -> Option<Location>;
    fn value<'v, V: Value<'v>>(&self) -> Option<V> where 'n: 'v;
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestStorage<V> {
        storage: Vec<V>,
    }

    impl<'s, 'v, V> SlottedStorage<'s, 'v, V> for TestStorage<V> where V: Copy {
        type Error = PageError;
    
        fn get_value(&'v self, index: u8) -> Result<V, Self::Error> {
            Ok(self.storage[index as usize])
        }
    }

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    struct TestNode<'n>(&'n [u8; 1 + 64 + 16 * 8]);

    impl<'n> TestNode<'n> {
        fn new(value: &'n [u8; 1 + 64 + 16 * 8]) -> Self {
            Self(value)
        }
    }

    impl<'n> Node<'n> for TestNode<'n> {
        fn prefix(&self) -> Nibbles {
            Nibbles::new()
        }

        fn child(&self, _index: u8) -> Option<Location> {
            None
        }

        fn value<'v, V: Value<'v>>(&self) -> Option<V> where 'n: 'v {
            None
        }
    }

    impl<'n> Value<'n> for TestNode<'n> {}

    impl<'n> TryFrom<&'n [u8]> for TestNode<'n> {
        type Error = PageError;

        fn try_from(value: &'n [u8]) -> Result<Self, Self::Error> {
            Ok(TestNode(value.try_into().unwrap()))
        }
    }

    impl<'n> TryInto<&'n [u8]> for TestNode<'n> {
        type Error = PageError;

        fn try_into(self) -> Result<&'n [u8], Self::Error> {
            Ok(self.0)
        }
    }
    
    #[test]
    fn test_traverse_path() {
        let storage = TestStorage { storage: vec![TestNode::new(&[0; 1 + 64 + 16 * 8])] };
        let subtrie_page = SubtriePage::from(storage);
        let path = Nibbles::new();
        let result = subtrie_page.traverse_path(0, &path);
        assert!(result.is_ok());
        let (location, remaining_path) = result.unwrap().unwrap();
        assert_eq!(location, Location::for_cell(0));
        assert_eq!(remaining_path, Nibbles::new());
    }
}
