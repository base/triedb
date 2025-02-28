use metrics::Histogram;
use metrics_derive::Metrics;

#[derive(Metrics, Clone)]
#[metrics(scope = "triedb")]
pub struct DatabaseMetrics {
    /// The number of pages read by a read-only transaction
    #[metrics(describe = "The number of pages read by a read-only transaction")]
    pub(crate) ro_transaction_pages_read: Histogram,
    /// The number of pages written by a read-write transaction
    #[metrics(describe = "The number of pages written by a read-write transaction")]
    pub(crate) rw_transaction_pages_written: Histogram,
    /// The number of pages read by a read-write transaction
    #[metrics(describe = "The number of pages read by a read-write transaction")]
    pub(crate) rw_transaction_pages_read: Histogram,
    /// The number of pages allocated by a read-write transaction
    #[metrics(describe = "The number of pages allocated by a read-write transaction")]
    pub(crate) rw_transaction_pages_allocated: Histogram,
}

#[derive(Debug, Default, Clone)]
pub(crate) struct TransactionMetrics {
    pub(crate) pages_read: u32,
    pub(crate) pages_written: u32,
    pub(crate) pages_allocated: u32,
    pub(crate) pages_reallocated: u32,
    // TODO: add more metrics
}
