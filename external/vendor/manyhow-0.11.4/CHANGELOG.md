# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<!-- ## [Unreleased] -->
## [0.11.4] - 2024-08-25
- Updated `proc-macro-utils`

## [0.11.3] - 2024-07-30
### Added
- implementations of `Add` and `AddAssign` to `manyhow::Error`/`manyhow::ErrorMessage`

## [0.11.2] - 2024-07-20
### Fixed
- adjusted spans for `#[manyhow]` on `use` items to make go-to-definition work better.

## [0.11.1] - 2024-03-16
### Fixed
- fix `item_as_dummy` for attribute macros

## [0.11.0] - 2024-01-27
### Added
- `{Function,Attribute,Derive}MacroHandler`,

### Removed
- **Breaking Change** `MacroHandler` was replaced by dedicated traits for each macro type, this probably doesn't affect any usages

### Fixed
- `syn::Result` could not be used as return type of macro handlers

## [0.10.4] - 2023-11-24
### Changed
- Allow parsing of types that do not implement `ToTokens`

## [0.10.3] - 2023-11-23
### Added
- `impl SpanRanged for Range<impl SpanRanged>`

## [0.10.2] - 2023-11-20
### Added
- `SpanRanged::span_joined` a function to return joined spans on nightly (to replace `SpanRanged::joined`).

## [0.10.1] - 2023-11-20
### Added
- `SpanRanged::joined` a function to return joined spans on nightly.
## [0.10.0] - 2023-11-13
### Added
- support `(impl ToTokens, impl ToTokens)` tuples for span range

## [0.9.0] - 2023-11-06
### Added
- support `impl Parse` inputs and `impl ToTokens` outputs.
- added macro alternatives to the `function()`, `derive()` and `attribute()` functions to support `impl Parse/ToTokens`.

## [0.8.1] - 2023-09-17
### Fixed
- `ensure!(let...)` had compile error in its expansion.

## [0.8.0] - 2023-09-17
### Changed
- `ensure!` now supports `let ... = ...` as condition.

## [0.7.0] - 2023-09-17
### Added
- `ensure!` macro.

## [0.6.0] - 2023-09-09
### Added
- Support attribute on use statement of function.
- Support `#[manyhow(proc_macro*)]` to specify proc-macro kind

## [0.5.1] - 2023-07-21
Something went wrong with previous release.

## [0.5.0] - 2023-07-20
### Added
- `Emitter::new()` and `Emitter::into_error()` to enable using the Emitter manually.
- Implemented `Extend` for `Emitter` and `Error`.
- Added `emit!` macro for adding errors to `Emitter`.
- Added support for converting `darling::Error` to `manyhow::Error` (available via `darling` feature).

### Changed
- **Breaking Change** replaced `Emitter::fail_if_dirty` with `Emitter::into_result`.

## [0.4.2] - 2023-05-15
### Fixed
- `ToTokens`' `SpanRange` conversion should work without `proc_macro`.

## [0.4.1] - 2023-05-14
### Fixed
- `manyhow_macros` version

## [0.4.0] - 2023-05-14
### Added
- `impl_fn` flag to create separate implementation function types.

## [0.3.0] - 2023-05-02
### Added
- `SpanRanged` implementation for `Option<impl SpanRanged>`.

## [0.2.0] - 2023-04-19
### Changed
- Moved `Error::join` to `JoinToTokensError` trait.

## [0.1.1] - 2023-04-16
Only documentation changes.

## [v0.1.0] 
**Initial Release**

[unreleased]: https://github.com/ModProg/manyhow/compare/v0.11.4...HEAD
[0.11.4]: https://github.com/ModProg/manyhow/compare/v0.11.3...v0.11.4
[0.11.3]: https://github.com/ModProg/manyhow/compare/v0.11.2...v0.11.3
[0.11.2]: https://github.com/ModProg/manyhow/compare/v0.11.1...v0.11.2
[0.11.1]: https://github.com/ModProg/manyhow/compare/v0.11.0...v0.11.1
[0.11.0]: https://github.com/ModProg/manyhow/compare/v0.10.4...v0.11.0
[0.10.4]: https://github.com/ModProg/manyhow/compare/v0.10.3...v0.10.4
[0.10.3]: https://github.com/ModProg/manyhow/compare/v0.10.2...v0.10.3
[0.10.2]: https://github.com/ModProg/manyhow/compare/v0.10.1...v0.10.2
[0.10.1]: https://github.com/ModProg/manyhow/compare/v0.10.0...v0.10.1
[0.10.0]: https://github.com/ModProg/manyhow/compare/v0.9.0...v0.10.0
[0.9.0]: https://github.com/ModProg/manyhow/compare/v0.8.1...v0.9.0
[0.8.1]: https://github.com/ModProg/manyhow/compare/v0.8.0...v0.8.1
[0.8.0]: https://github.com/ModProg/manyhow/compare/v0.7.0...v0.8.0
[0.7.0]: https://github.com/ModProg/manyhow/compare/v0.6.0...v0.7.0
[0.6.0]: https://github.com/ModProg/manyhow/compare/v0.5.1...v0.6.0
[0.5.1]: https://github.com/ModProg/manyhow/compare/v0.5.0...v0.5.1
[0.5.0]: https://github.com/ModProg/manyhow/compare/v0.4.2...v0.5.0
[0.4.2]: https://github.com/ModProg/manyhow/compare/v0.4.1...v0.4.2
[0.4.1]: https://github.com/ModProg/manyhow/compare/v0.4.0...v0.4.1
[0.4.0]: https://github.com/ModProg/manyhow/compare/v0.3.0...v0.4.0
[0.3.0]: https://github.com/ModProg/manyhow/compare/v0.2.0...v0.3.0
[0.2.0]: https://github.com/ModProg/manyhow/compare/v0.1.1...v0.2.0
[0.1.1]: https://github.com/ModProg/manyhow/compare/v0.1.0...v0.1.1
[v0.1.0]: https://github.com/ModProg/manyhow/tree/v0.1.0
