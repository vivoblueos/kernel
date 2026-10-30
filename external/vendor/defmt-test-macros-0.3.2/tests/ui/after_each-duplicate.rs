fn main() {}

#[defmt_test_macros::tests]
mod tests {
    #[after_each]
    fn first() {}

    #[after_each]
    fn second() {}
}
