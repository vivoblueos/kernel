fn main() {}

#[defmt_test_macros::tests]
mod tests {
    #[teardown]
    fn say(name: &str) {
        assert_eq!("name", name);
    }
}
