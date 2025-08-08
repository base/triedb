use crate::executor::{Executor, Future};

/// A dummy executor that executes all functions in the same thread.
#[derive(Copy, Clone, Debug)]
pub struct Inline;

impl Executor for Inline {
    #[inline]
    fn defer<F, T>(&self, f: F) -> Future<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + Sync + 'static,
    {
        Future::ready(f())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::Wait;

    #[test]
    fn defer() {
        let inline = Inline;
        let future = inline.defer(|| 123);
        assert_eq!(future.wait(), &123);
    }
}
