use crate::executor::Future;

/// Trait for objects that can be awaited until they reach their final state.
///
/// The main structure that implements this trait is [`Future`], but also any structure that wraps
/// a `Future` may implement this trait.
pub trait Wait {
    type Output;

    /// Blocks execution until the final state is reached.
    fn wait(&self) -> &Self::Output;
}

/// Trait for objects that can run functions concurrently.
pub trait Executor {
    /// Runs the given closure `f` in a separate thread, and returns a [`Future`] that can be used
    /// to obtain the result of `f` once its execution is complete.
    fn defer<F, T>(&self, f: F) -> Future<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + Sync + 'static;
}

impl<E: Executor> Executor for &E {
    #[inline]
    fn defer<F, T>(&self, f: F) -> Future<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + Sync + 'static,
    {
        (**self).defer(f)
    }
}
