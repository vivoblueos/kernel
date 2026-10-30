fn main() {}

#[defmt_test_macros::tests]
mod tests {
    #[before_each]
    fn first() {}

    #[before_each]
    fn second() {}
}
