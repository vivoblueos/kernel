use cortex_m_rt as _;
use cortex_m_semihosting::debug;
pub use defmt::info;

use crate::TestOutcome;

/// Terminates the application and makes a semihosting-capable debug tool exit
/// with status code 0.
pub fn exit() -> ! {
    loop {
        debug::exit(debug::EXIT_SUCCESS);
    }
}

pub fn check_outcome<T: TestOutcome>(outcome: T, should_error: bool) {
    if outcome.is_success() == should_error {
        let note = if should_error {
            defmt::intern!("`#[should_error]` ")
        } else {
            defmt::intern!("")
        };
        defmt::panic!("{}test failed with outcome: {}", note, outcome);
    }
}
