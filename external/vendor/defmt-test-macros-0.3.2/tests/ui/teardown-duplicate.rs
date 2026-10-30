fn main() {}

#[defmt_test_macros::tests]
mod tests {
    #[teardown]
    fn first() {}

    #[teardown]
    fn second() {}
}
