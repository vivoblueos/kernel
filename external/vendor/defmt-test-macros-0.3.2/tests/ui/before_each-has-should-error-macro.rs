fn main() {}

#[defmt_test_macros::tests]
mod tests {
    #[before_each]
    #[should_error]
    fn init() {}
}
