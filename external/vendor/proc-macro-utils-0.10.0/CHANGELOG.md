# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<!-- ## [Unreleased] -->

## [0.10.0] - 2024-05-21
### Changed
- `next_expression()` stops at `=>` as well, matching `macro_rule`'s `expr`

## [0.9.1] - 2024-03-13
### Added
- `span()` to `TokenParser`.

## [0.9.0] - 2024-03-13
### Added
- `*_tt` functions to `TokenParser`.
- `next_macro_rules_tt()` to `TokenParser`.
- `TokenTreeLiteral` with `is_string()` and `string()`.

### Changed
- **Breaking Change** Sealed extension traits.

### Fixed
- `assert_expansion!` was failing on nightly.

## [0.8.0] - 2023-05-14
### Fixed
- bumped `smallvec` version to `1.5` to avoid nightly feature compilation issues.

## [0.7.0] - 2023-05-14
- Increased documentation and test coverage.

### Added
- `quote::ToTokens` implementation for `TokenParser` (`quote` is a new default feature).
- `peek_{token}` and `peek_n_{token}` to `TokenParser`.
- `alone` to `TokenTreePunct` ensuring if a token is `Punct` its `spacing` is `Alone`
- `*_alone` functions to `TokenParser` setting the last token to `Alone` if it is a punctuation.
- `next_n` to `TokenParser` returning the next `n` tokens.
- `peek_range` to `TokenParser` returning a range of tokens.
- `FromStr` implementation for `TokenParser` based on `TokenStream`'s.
- `assert_expansion!` macro to unit test macro implementations.

### Changed
- **Breaking Change** Added const generic buffer size to `TokenParser`.
- **Breaking Change** `Peeker::peek` takes `&[TokenTree]` instead of `TokenParser`.
- **Breaking Change** `Peeker::LENGTH` is function `len` now.
- **Breaking Change** `*_{delimiter}` returns `Group` instead of the contained stream.
  To get to the stream call `.stream()`
- **Breaking Change** `TokenParser::*_{punctuation}` got renamed to `*_tt_{punctuation}` and their behaviour was changed to match that of `$tt` in macro_rules instead of requiring `Spacing::Alone`, returned `spacing` is set to `Alone`.
- `TokenParser` peeking supports `n` greater than stack buffer, allowing spilling to heap.
- Increased default `TokenParser` peek buffer to `6`.
- Marked parser functions as must_use.
- `next_expr` and `next_type` set the last tokens `spacing` to `Alone`.

### Fixed
- Allow `assert_tokens` in expression position e.g. unbraced `match` arm

## [0.6.0] - 2023-04-29
- `TokenParser::next_keyword(v)`

## [0.5.2] - 2023-04-06
### Fixed
- `TokenParser::peek_n()` always returned `None`
- `TokenParser::next_{token}` did not work correctly because of `peek_n`

## [0.5.1] - 2023-03-02
### Fixed
- `TokenParser::next_string()` did not consume token

## [0.5.0] - 2023-03-01
### Added
- `TokenParser` for parsing simple rust structures
- `assert_tokens!` macro
- `TokenTreeExt::into_<token>()` functions 
- `Delimited` trait for accessing `TokenTree::Group`

### Changed
- **Breaking Change** `TokenTreeExt::<token>()` now return references

[unreleased]: https://github.com/ModProg/proc-macro-utils/compare/v0.10.0...HEAD
[0.10.0]: https://github.com/ModProg/proc-macro-utils/compare/v0.9.1...v0.10.0
[0.9.1]: https://github.com/ModProg/proc-macro-utils/compare/v0.9.0...v0.9.1
[0.9.0]: https://github.com/ModProg/proc-macro-utils/compare/v0.8.0...v0.9.0
[0.8.0]: https://github.com/ModProg/proc-macro-utils/compare/v0.7.0...v0.8.0
[0.7.0]: https://github.com/ModProg/proc-macro-utils/compare/v0.6.0...v0.7.0
[0.6.0]: https://github.com/ModProg/proc-macro-utils/compare/v0.5.2...v0.6.0
[0.5.2]: https://github.com/ModProg/proc-macro-utils/compare/v0.5.1...v0.5.2
[0.5.1]: https://github.com/ModProg/proc-macro-utils/compare/v0.5.0...v0.5.1
[0.5.0]: https://github.com/ModProg/proc-macro-utils/compare/v0.4.0...v0.5.0
