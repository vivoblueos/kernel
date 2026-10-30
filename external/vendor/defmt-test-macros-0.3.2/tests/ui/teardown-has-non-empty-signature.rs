fn main() {}

#[defmt_test_macros::tests]
mod tests {
    #[init]
    fn init() {
        // empty
    }

    #[teardown]
    fn teardown(arg: &mut u8) {
        assert!(true);
    }
}
