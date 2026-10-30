# [Unreleased]

# [v0.3.3]

- [#917] feat: add teardown fn for defmt-test

[#917]: https://github.com/knurling-rs/defmt/pull/917

# [v0.3.2]

Updates `defmt-test-macros` and therefore actually support [#696].

# [v0.3.1]

- [#786]: `defmt-test`: Exit with semihosting exit
- [#698] Expose number of tests with `DEFMT_TEST_COUNT` symbol in test artifact for other tools to pick up
- [#696] Add `#[before_each]` and `#[after_each]` attributes

[#786]: https://github.com/knurling-rs/defmt/pull/786
[#698]: https://github.com/knurling-rs/defmt/pull/698
[#696]: https://github.com/knurling-rs/defmt/pull/696

# [v0.3.0]

No changes.

# [v0.2.3]

- [#441] Support more items in `#[tests]` modules

[#441]: https://github.com/knurling-rs/defmt/pull/441

# [v0.2.2]

- [#436] `README.md`: Remove outdated setup steps
- [#421] `README.md`: Update dependency version & use `defmt::assert()` and `defmt::assert_eq()` in the example

[#421]: https://github.com/knurling-rs/defmt/pull/421
[#436]: https://github.com/knurling-rs/defmt/pull/436

# [v0.2.1]

- [#418] Bump `defmt-test-macros` to `v0.2.0`
- [#414] `README.md`: Extend introduction
- [#410] Add Knurling-rs logo to API docs

[#410]: https://github.com/knurling-rs/defmt/pull/410
[#414]: https://github.com/knurling-rs/defmt/pull/414
[#418]: https://github.com/knurling-rs/defmt/pull/418
# [v0.2.0]

- [#383] Modify attributes in place and handle `#[cfg]`

[#383]: https://github.com/knurling-rs/defmt/pull/383

# [v0.1.1]

- [#297] Display the number of tests as they are executed.
- [#294] Allow `use` items inside the test module.

[#294]: https://github.com/knurling-rs/defmt/pull/294
[#297]: https://github.com/knurling-rs/defmt/pull/297
# v0.1.0

Initial release.

[Unreleased]: https://github.com/knurling-rs/defmt/compare/defmt-test-v0.3.3...main
[v0.3.3]: https://github.com/knurling-rs/defmt/compare/defmt-test-v0.3.2...defmt-test-v0.3.3
[v0.3.2]: https://github.com/knurling-rs/defmt/compare/defmt-test-v0.3.1...defmt-test-v0.3.2
[v0.3.1]: https://github.com/knurling-rs/defmt/compare/defmt-test-v0.3.0...defmt-test-v0.3.1
[v0.3.0]: https://github.com/knurling-rs/defmt/compare/defmt-test-v0.2.3...defmt-test-v0.3.0
[v0.2.3]: https://github.com/knurling-rs/defmt/compare/defmt-test-v0.2.2...defmt-test-v0.2.3
[v0.2.2]: https://github.com/knurling-rs/defmt/compare/defmt-test-v0.2.1...defmt-test-v0.2.2
[v0.2.1]: https://github.com/knurling-rs/defmt/compare/defmt-test-v0.2.0...defmt-test-v0.2.1
[v0.2.0]: https://github.com/knurling-rs/defmt/compare/defmt-test-v0.1.1...defmt-test-v0.2.0
[v0.1.1]: https://github.com/knurling-rs/defmt/compare/defmt-test-v0.1.0...defmt-test-v0.1.1
