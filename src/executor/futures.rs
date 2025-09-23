use crate::executor::Wait;
use std::{
    fmt,
    sync::{Arc, OnceLock},
};

#[derive(Debug)]
enum FutureStatus<T> {
    Completed(T),
    Poisoned,
}

use FutureStatus::*;

/// A placeholder for a value that will be computed at a later time.
///
/// `Future`s are the result of running functions in separate threads using
/// [`Executor::spawn`](crate::executor::Executor::spawn): calling `spawn()` in fact returns
/// immediately, even though the function will complete at a later time. The `Future` returned by
/// `spawn()` allows retrieving the result of the function once it completes.
///
/// # Poisoning
///
/// A `Future` may be in a "poisoned" status if the execution of the function that produced it
/// failed with a panic.
pub struct Future<T> {
    cell: Arc<OnceLock<FutureStatus<T>>>,
}

impl<T> Future<T> {
    #[inline]
    #[must_use]
    pub(super) fn pending() -> Self {
        Self { cell: Arc::new(OnceLock::new()) }
    }

    /// Creates a new `Future` that is already completed with the given value.
    #[inline]
    #[must_use]
    pub fn ready(value: T) -> Self {
        let this = Self::pending();
        this.complete(value);
        this
    }

    #[inline]
    pub(super) fn complete(&self, value: T) {
        self.try_complete(value).unwrap_or_else(|err| panic!("{err}"))
    }

    #[inline]
    pub(super) fn try_complete(&self, value: T) -> Result<(), ReadyError> {
        self.cell.set(Completed(value)).map_err(|_| ReadyError)
    }

    // There's no `poison()` method simply because it's not used internally.

    #[inline]
    pub(super) fn try_poison(&self) -> Result<(), ReadyError> {
        self.cell.set(Poisoned).map_err(|_| ReadyError)
    }

    /// Returns the value of the `Future`, or `None` if this `Future` was not completed yet.
    ///
    /// # Panics
    ///
    /// If the `Future` is poisoned. See [`Future::try_get()`] for a non-panicking version of this
    /// method.
    #[inline]
    #[must_use]
    pub fn get(&self) -> Option<&T> {
        self.try_get().map(|result| result.expect("Future is poisoned"))
    }

    /// Returns the value of the `Future`, `None` if this `Future` was not completed yet, or an
    /// error if this `Future` is poisoned.
    #[inline]
    #[must_use]
    pub fn try_get(&self) -> Option<Result<&T, PoisonError>> {
        match self.cell.get() {
            None => None,
            Some(Completed(ref value)) => Some(Ok(value)),
            Some(Poisoned) => Some(Err(PoisonError)),
        }
    }
}

impl<T> Wait for Future<T> {
    type Output = T;

    #[inline]
    fn wait(&self) -> &Self::Output {
        match self.cell.wait() {
            Completed(value) => value,
            Poisoned => panic!("{PoisonError}"),
        }
    }
}

impl<T> Clone for Future<T> {
    fn clone(&self) -> Self {
        Self { cell: Arc::clone(&self.cell) }
    }
}

impl<T: fmt::Debug> fmt::Debug for Future<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct Pending(*const ());

        impl fmt::Debug for Pending {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "<pending @ {:?}>", self.0)
            }
        }

        struct Poisoned;

        impl fmt::Debug for Poisoned {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("<poisoned>")
            }
        }

        let p = Arc::as_ptr(&self.cell) as *const ();
        let p = Pending(p);

        f.debug_tuple("Future")
            .field(match self.try_get() {
                None => &p,
                Some(Ok(value)) => value,
                Some(Err(PoisonError)) => &Poisoned,
            })
            .finish()
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub(super) struct ReadyError;

impl fmt::Display for ReadyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("attempted to complete or poison the Future twice")
    }
}

impl std::error::Error for ReadyError {}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PoisonError;

impl fmt::Display for PoisonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("execution of the closure for this Future resulted in a panic")
    }
}

impl std::error::Error for PoisonError {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{panic, sync::Barrier, thread, time::Duration};

    #[test]
    fn pending_to_completed() {
        let f = Future::<u32>::pending();

        assert_eq!(f.get(), None);
        assert_eq!(f.try_get(), None);

        f.complete(123);

        assert_eq!(f.get(), Some(&123));
        assert_eq!(f.try_get(), Some(Ok(&123)));
    }

    #[test]
    fn pending_to_poisoned() {
        let f = Future::<u32>::pending();

        assert_eq!(f.get(), None);
        assert_eq!(f.try_get(), None);

        f.try_poison().expect("poison failed");

        panic::catch_unwind(|| f.get()).expect_err("get() should have panicked");
        assert_eq!(f.try_get(), Some(Err(PoisonError)));
    }

    #[test]
    fn wait() {
        let f = Future::<u32>::pending();
        let g = f.clone();
        let barrier = Barrier::new(2);

        thread::scope(|s| {
            s.spawn(|| {
                barrier.wait();
                thread::sleep(Duration::from_secs(1));
                g.complete(123);
            });

            assert_eq!(f.get(), None);
            assert_eq!(f.try_get(), None);

            barrier.wait();

            assert_eq!(f.wait(), &123);
            assert_eq!(f.get(), Some(&123));
            assert_eq!(f.try_get(), Some(Ok(&123)));

            // Waiting twice or more should return the same value
            assert_eq!(f.wait(), &123);
        });
    }
}
