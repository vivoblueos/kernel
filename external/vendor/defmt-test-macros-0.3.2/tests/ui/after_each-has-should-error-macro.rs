fn main() {}

#[defmt_test_macros::tests]
mod tests {
    #[after_each]
    #[should_error]
    fn init() {}
}
