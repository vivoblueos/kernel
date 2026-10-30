# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

## [v0.1.3] - 2020-07-07

This release of the 0.1 version exists for compatibility with 1.0.0.
There are no functional changes compared to 0.1.2.

## [v0.1.2] - 2019-04-21

### Added

- `Error<E>` gained a `map` method that lets you transform the error in the
  `Error::Other` variant into a different type.

- `Error<E>` now implements the `From<E>` trait.

## [v0.1.1] - 2018-01-10

### Fixed

- The `await!` macro now works when the expression `$e` mutably borrows `self`.

## v0.1.0 - 2018-01-10

Initial release

[Unreleased]: https://github.com/rust-embedded/nb/compare/v0.1.3...HEAD
[v0.1.3]: https://github.com/rust-embedded/nb/compare/v0.1.2...v0.1.3
[v0.1.2]: https://github.com/rust-embedded/nb/compare/v0.1.1...v0.1.2
[v0.1.1]: https://github.com/rust-embedded/nb/compare/v0.1.0...v0.1.1
