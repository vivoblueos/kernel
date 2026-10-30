# Change Log

All notable changes to this project will be documented in this file.
This project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

## [v0.2.5] - 2019-08-29

### Changed

- The `const-fn` feature is now stable

## [v0.2.4] - 2018-10-30

### Added

- Note in the documentation that `Mutex` is not memory safe in multi-core systems.

### Changed

- The `const-fn` feature can now be used on 1.31-beta and will also work on stable 1.31.

## [v0.2.3] - 2018-08-17

### Fixed

- A compilation error when using a recent nightly while the "const-fn" feature was enabled.

## [v0.2.2] - 2018-08-17 - YANKED

### Fixed

- A compilation error when using a recent nightly while the "const-fn" feature was enabled.

## [v0.2.1] - 2018-08-03

### Fixed

- Soundness issue where it was possible to borrow the contents of a Mutex for longer than the
  lifetime of the Mutex.

## [v0.2.0] - 2018-05-10 - YANKED

YANKED due to a soundness issue: see v0.2.1 for details

### Changed

- [breaking-change] `const-fn` is no longer a default feature (i.e. a feature that's enabled by
  default). The consequence is that this crate now compiles on 1.27 (beta) by default, and opting
  into `const-fn` requires nightly.

## [v0.1.2] - 2018-04-24

### Added

- An opt-out "const-fn" Cargo feature. When this feature is disabled this crate compiles on stable.

## [v0.1.1] - 2017-09-19

### Fixed

- Added feature gate to make this work on recent nightlies

## v0.1.0 - 2017-07-06

- Initial release

[Unreleased]: https://github.com/japaric/bare-metal/compare/v0.2.5...HEAD
[v0.2.5]: https://github.com/japaric/bare-metal/compare/v0.2.4...v0.2.5
[v0.2.4]: https://github.com/japaric/bare-metal/compare/v0.2.3...v0.2.4
[v0.2.3]: https://github.com/japaric/bare-metal/compare/v0.2.2...v0.2.3
[v0.2.2]: https://github.com/japaric/bare-metal/compare/v0.2.1...v0.2.2
[v0.2.1]: https://github.com/japaric/bare-metal/compare/v0.2.0...v0.2.1
[v0.2.0]: https://github.com/japaric/bare-metal/compare/v0.1.2...v0.2.0
[v0.1.2]: https://github.com/japaric/bare-metal/compare/v0.1.1...v0.1.2
[v0.1.1]: https://github.com/japaric/bare-metal/compare/v0.1.0...v0.1.1
