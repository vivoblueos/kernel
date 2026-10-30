fn main() {}

#[defmt_test_macros::tests]
mod tests {
    #[init]
    fn init() {
        // empty
    }

    #[test]
    fn test(arg: &mut u8) {
        assert!(true);
    }
}
