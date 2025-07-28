#![cfg(test)]

use crate::executor::{Executor, Future};

/// A dummy executor that never executes any function.
#[derive(Copy, Clone, Debug)]
pub(crate) struct Never;

impl Executor for Never {
    #[inline]
    fn defer<F, T>(&self, _: F) -> Future<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + Sync + 'static,
    {
        Future::pending()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defer() {
        let never = Never;
        let future = never.defer(|| 123);
        assert_eq!(future.get(), None);
    }
}
