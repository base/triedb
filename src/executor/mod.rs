//! Concurrent execution.
//!
//! This module provides structures and traits to run functions in separate threads and obtain
//! their results later on. The implementation is currently based on the popular [`rayon`] crate.
//! This module also provides a dummy implementation called [`Inline`] that does not spawn any
//! actual thread but executes everything serially.
//!
//! # Examples
//!
//! ```
//! use triedb::executor::{threadpool, Executor, Wait};
//!
//! // Create a thread pool
//! let pool = threadpool::builder().build().unwrap();
//!
//! // Run some closures in the background.
//! let future1 = pool.defer(|| 1 + 1);
//! let future2 = pool.defer(|| 2 + 2);
//!
//! // Wait for the closures to return a result.
//! assert_eq!(future1.wait(), &2);
//! assert_eq!(future2.wait(), &4);
//! ```

mod futures;
mod inline;
mod never;
mod traits;

pub mod threadpool;

pub use futures::{Future, PoisonError};
pub use inline::Inline;
pub use traits::{Executor, Wait};

#[cfg(test)]
pub(crate) use never::Never;
