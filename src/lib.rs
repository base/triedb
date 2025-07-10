#![warn(clippy::dbg_macro)]
#![warn(clippy::print_stderr)]
#![warn(clippy::print_stdout)]
#![warn(missing_debug_implementations)]
#![warn(unnameable_types)]
#![warn(unreachable_pub)]
#![warn(unused_macro_rules)]
// TODO: temporary allow these warnings so that we can enforce clippy rules
#![allow(clippy::module_inception)]
#![allow(clippy::too_many_arguments)]

pub mod account;
pub mod config;
pub mod context;
pub mod database;
pub mod executor;
pub mod location;
pub mod meta;
pub mod metrics;
pub mod node;
pub mod page;
pub mod path;
pub mod pointer;
pub mod snapshot;
pub mod storage;
pub mod transaction;

pub use config::Config;
pub use database::Database;
pub use page::PageManager;
