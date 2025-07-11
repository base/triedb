use std::time::Duration;

/// Configurable metrics collector
#[derive(Debug, Clone)]
pub struct MetricsCollector {
    /// Enable/disable collecting metrics
    pub enabled: bool,    
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

impl Default for MetricsCollector {
    fn default() -> Self {
        Self {
            enabled: true,
            transaction_metrics: true,
            database_metrics: true,
            resource_metrics: true,
            interval: Duration::from_secs(30),
            state_root_timing_metrics: true,
        }
    }
}