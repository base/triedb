use log::{Level, Log, Metadata, Record};
use std::io::Write;

/// A configurable logger.
#[derive(Debug)]
pub struct Logger;

impl Log for Logger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.level() <= Level::Info
    }

    fn log(&self, record: &Record) {
        if self.enabled(record.metadata()) {
            let _ = writeln!(
                std::io::stdout(),
                "[{}] {} - {}",
                record.level(),
                record.target(),
                record.args()
            );
        }
    }

    fn flush(&self) {
        std::io::stdout().flush().unwrap();
    }
}
