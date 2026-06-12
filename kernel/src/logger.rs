use crate::{arch, kprintln, scheduler, time};
use blueos_logger::{self, LogWriter};
use log::Record;

fn log_writer(record: &Record) {
    let timestamp = time::now().as_millis();
    let tid = scheduler::current_thread_id();
    let cpu = arch::current_cpu_id();
    #[cfg(not(test))]
    kprintln!(
        "[T:{:09} C:{} TH:0x{:x}][{}] {} ",
        timestamp,
        cpu,
        tid,
        record.level(),
        record.args()
    );
    #[cfg(test)]
    semihosting::println!(
        "[T:{:09} C:{} TH:0x{:x}][{}] {} ",
        timestamp,
        cpu,
        tid,
        record.level(),
        record.args()
    );
}

/// Initialize the kernel logger.
pub fn logger_init() {
    blueos_logger::logger_init(log_writer as LogWriter);
}