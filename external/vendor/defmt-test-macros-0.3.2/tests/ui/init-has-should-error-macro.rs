fn main() {}

#[defmt_test_macros::tests]
mod tests {
    #[init]
    #[should_error]
    fn init() {}
}
