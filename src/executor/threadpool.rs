use crate::executor::{Executor, Future};
use rayon::{ThreadPool, ThreadPoolBuilder};
use std::thread;

/// A wrapper around [`ThreadPoolBuilder::new()`] which sets some default values to make the
/// resulting [`ThreadPool`] play nicely with the [`Executor`] trait.
pub fn builder() -> ThreadPoolBuilder {
    ThreadPoolBuilder::new()
        .thread_name(|num| format!("executor-thread-{num:03}"))
        // The default behavior for `rayon` is to abort in case of panic, causing the whole program
        // to crash. We instead want to catch individual panics and poison the relevant `Future`
        // when those occur.
        //
        // This panic hanlder does nothing, so that the abort behavior is suppressed. We don't need
        // to explicitly print an error message or the backtrace because this will be already taken
        // care of.
        .panic_handler(|_| {})
}

impl Executor for ThreadPool {
    fn defer<F, T>(&self, f: F) -> Future<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + Sync + 'static,
    {
        let sender_future = Future::pending();
        let receiver_future = sender_future.clone();

        self.spawn(move || {
            // Create the guard panic first, then run the closure. The guard will be dropped at the
            // end of this scope. If the function succeeds, the guard won't do anything; if it
            // panics, the guard's `Drop` implementation will poison the future.
            let _guard = PanicGuard { future: &sender_future };
            sender_future.complete(f())
        });

        receiver_future
    }
}

/// A "guard" to detect if this thread panics, and poison the `Future` in that case.
#[derive(Debug)]
struct PanicGuard<'a, T> {
    future: &'a Future<T>,
}

impl<'a, T> Drop for PanicGuard<'a, T> {
    fn drop(&mut self) {
        if thread::panicking() {
            // Unlikely, but if the future was already set, just ignore the error from
            // `try_poison()` and carry on
            let _ = self.future.try_poison();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::{PoisonError, Wait};
    use std::panic;

    #[test]
    #[cfg_attr(miri, ignore = "crossbeam (used by rayon) does not play nicely with miri")]
    fn defer() {
        let pool = builder().build().expect("building thread pool failed");
        let future = pool.defer(|| 123);
        assert_eq!(future.wait(), &123);
    }

    #[test]
    #[cfg_attr(miri, ignore = "crossbeam (used by rayon) does not play nicely with miri")]
    fn poisoning() {
        let pool = builder().build().expect("building thread pool failed");
        let future = pool.defer(|| panic!("something went wrong"));
        panic::catch_unwind(|| future.wait()).expect_err("wait() was expected to panic");
        assert_eq!(future.try_get(), Some(Err(PoisonError)));
    }
}
