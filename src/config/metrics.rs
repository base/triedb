use std::time::Duration;

/// Configurable metrics collector
#[derive(Debug, Clone)]
pub struct MetricsCollector {
    /// Enable/disable transaction metrics
    pub transaction_metrics: bool,
    /// Enable/disable database metrics  
    pub database_metrics: bool,
    /// Enable/disable resource usage metrics (memory, disk I/O patterns)
    pub resource_metrics: bool,
    /// Frequency of metrics collection
    pub interval: Duration,
    /// Enable/disable state root computation timing
    pub state_root_timing_metrics: bool,
}

impl MetricsCollector {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_transaction_metrics(mut self, transaction_metrics: bool) -> Self {
        self.transaction_metrics = transaction_metrics;
        self
    }

    pub fn with_database_metrics(mut self, database_metrics: bool) -> Self {
        self.database_metrics = database_metrics;   
        self
    }

    pub fn with_resource_metrics(mut self, resource_metrics: bool) -> Self {
        self.resource_metrics = resource_metrics;
        self
    }

    pub fn with_interval(mut self, interval: Duration) -> Self {
        self.interval = interval;
        self
    }

    pub fn with_state_root_timing_metrics(mut self, state_root_timing_metrics: bool) -> Self {
        self.state_root_timing_metrics = state_root_timing_metrics;
        self
    }
}

impl Default for MetricsCollector {
    fn default() -> Self {
        Self {
            transaction_metrics: true,
            database_metrics: true,
            resource_metrics: true,
            interval: Duration::from_secs(30),
            state_root_timing_metrics: true,
        }
    }
}