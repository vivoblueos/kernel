# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

### Added

### Fixed

### Changed

## [v0.3.9]

### Added

### Fixed

- No default feature from `serde`

### Changed

## [v0.3.8] - YANKED

### Added

- Optional `serde` support
- Optional `postcard` max size support

### Fixed

### Changed

## [v0.3.7]

### Added

- `Hz`, `kHz`, `MHz` shorthands for `Duration` and `nanos`, `micros`, `millis` for `Rate`
- `from_rate`, `from_duration` in addition to `into_duration`, `into_rate`;
- `const_try_from` in addition to `const_try_into`
- `<unit>_at_least` for ceil-rounded `Duration` convert
- Add `is_zero()` methods to `Duration<u32, NOM, DENOM>` and `Duration<u64, NOM, DENOM>` types to compare with zero without type conversion

### Fixed

### Changed

- Updated documentation of `const_cmp`

## [v0.3.6]

### Fixed

- Fixed error in conversion between large durations.
- Fixed `TimerRateU32` and `TimerRateU64` to use `Rate` instead of `Duration`

## [v0.3.5]

### Added

### Fixed

- Fixed `to_X` rates.

### Changed

## [v0.3.4] -- YANKED

### Added

- Add `Div` implementation for `Duration` and `Rate`
- Add `nanos()` methods and `NanosDuration` aliases alongside other units.
- Implement AddAssign and SubAssign for Instant and Duration, and
  MulAssign and DivAssign for Duration.
- Add `to_nanos()`, `to_micros()`, `to_millis()`, `to_secs()`, `to_minutes()`,
  and `to_hours()` methods to `Duration<u32, NOM, DENOM>` and
  `Duration<u64, NOM, DENOM>` types to easily convert to integer time units.
- Support for `Rate` (Hertz, Kilohertz, ...)

### Fixed

### Changed

## [v0.3.3]

### Changed

- Underlying const gcd implementation switched to the `gcd` crate.
- `Duration::convert` now `const`.

## [v0.3.2]

### Fixed

- `Duration::convert` did not do the right thing when getting close to maximum supported values.

## [v0.3.1]

### Added

- Added `CHANGELOG.md`

### Fixed

- Now supports a `defmt` version span (0.2 and 0.3 is supported)

[Unreleased]: https://github.com/korken89/fugit/compare/v0.3.9...HEAD
[v0.3.9]: https://github.com/korken89/fugit/compare/v0.3.8...v0.3.9
[v0.3.8]: https://github.com/korken89/fugit/compare/v0.3.7...v0.3.8
[v0.3.7]: https://github.com/korken89/fugit/compare/v0.3.6...v0.3.7
[v0.3.6]: https://github.com/korken89/fugit/compare/v0.3.5...v0.3.6
[v0.3.5]: https://github.com/korken89/fugit/compare/v0.3.4...v0.3.5
[v0.3.4]: https://github.com/korken89/fugit/compare/v0.3.3...v0.3.4
[v0.3.3]: https://github.com/korken89/fugit/compare/v0.3.2...v0.3.3
[v0.3.2]: https://github.com/korken89/fugit/compare/v0.3.1...v0.3.2
kv0.3.1]: https://github.com/korken89/fugit/compare/v0.3.0...v0.3.1
