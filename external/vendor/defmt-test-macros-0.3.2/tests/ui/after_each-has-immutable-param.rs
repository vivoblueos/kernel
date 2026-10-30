fn main() {}

#[defmt_test_macros::tests]
mod tests {
    #[after_each]
    fn say(name: &str) {
        assert_eq!("name", name);
    }
}
