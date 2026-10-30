fn main() {}

#[defmt_test_macros::tests]
mod tests {
    #[teardown]
    #[should_error]
    fn teardown() {}
}
