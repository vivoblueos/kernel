# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.3.0] - 2022-03-16

- Pinned `svgbob` to 0.6.6. (Fixes the compilation failure due to a breaking dependency change in `svgbob` 0.6.6.)

## [0.3.0-alpha.4] - 2021-12-18

- Added Consolas to the diagram font list.
- The macro now adds `transform: translate(0.5px, 0.5px)` to the root `svg` element to ensure pixel snapping on a low-DPI monitor.
- **Breaking** `#[svgbobdoc::transform]` was removed.
- **Breaking** Renamed `svgbobdoc::transform_mdstr!` to `svgbobdoc::transform!`.

## [0.3.0-alpha.3] - 2021-11-28

- Fixed the UAX #11 width calculation of texts including characters that are translated to XML entity references by `svgbob`.

## [0.3.0-alpha.2] - 2021-11-23

- **Breaking** Updated `svgbob` to 0.6.
- The version specification of `syn` is now more specific.
- Removed the dependency on `regex`.
- When the `enable` Cargo feature is not enabled, SVG images with unprocessed texts are produced instead of not transforming code blocks at all.
- Added support for `base64` 0.13.
- Code blocks now accept a link label (e.g., `~~~svgbob,[link-label]`, which can be inserted to a different location by `![link-label]`).

## [0.3.0-alpha.1] - 2021-07-23

- **Breaking** Updated `svgbob` to 0.5.
- **Breaking** Code blocks indented by more than three spaces are now processed.
- **Breaking** The macros are no-op by default. The `enable` Cargo feature must be enabled for the transformation to take place.
- Added `svgbobdoc::transform_mdstr!`.
- `#[svgbobdoc::transform]` is now deprecated.

## [0.2.3] - 2020-10-22

- Fixed the version specification of `lazy_static`.
- Unrecognized forms of `#[doc ...]` are now ignored. Examples:
    - `#[doc(cfg(windows))` ([rust-lang/rust#43781])
    - `#[doc(include = "external-file.md")]` ([rust-lang/rust#44732])
    - `#[doc(alias = "x")]` ([rust-lang/rust#50146])

[rust-lang/rust#43781]: https://github.com/rust-lang/rust/issues/43781
[rust-lang/rust#44732]: https://github.com/rust-lang/rust/issues/44732
[rust-lang/rust#50146]: https://github.com/rust-lang/rust/issues/50146

## [0.2.2] - 2020-03-30

- Upgraded `syn`, `quote`, and `proc-macro2` to 1.x.
- Added support for `base64` 0.11 and 0.12.

## [0.2.1] - 2020-01-08

- Added a maintenance status badge

## [0.2.0] - 2019-05-30

- **Breaking** Renamed `#[svgbobdoc::doc]` to `#[svgbobdoc::transform]` because it doesn't generate `#[doc = ...]` by itself but just transforms existing `#[doc = ...]`s.
- When attached to a struct, union, or enum, `#[transform]` now transforms its fields as they cannot have attribute macros by themselves.

## 0.1.0 - 2019-05-29

- Initial release.

[Unreleased]: https://github.com/yvt/svgbobdoc/compare/0.3.0-alpha.4...HEAD
[0.3.0-alpha.4]: https://github.com/yvt/svgbobdoc/compare/0.3.0-alpha.3...0.3.0-alpha.4
[0.3.0-alpha.3]: https://github.com/yvt/svgbobdoc/compare/0.3.0-alpha.2...0.3.0-alpha.3
[0.3.0-alpha.2]: https://github.com/yvt/svgbobdoc/compare/0.3.0-alpha.1...0.3.0-alpha.2
[0.3.0-alpha.1]: https://github.com/yvt/svgbobdoc/compare/0.2.3...0.3.0-alpha.1
[0.2.3]: https://github.com/yvt/svgbobdoc/compare/0.2.2...0.2.3
[0.2.2]: https://github.com/yvt/svgbobdoc/compare/0.2.1...0.2.2
[0.2.1]: https://github.com/yvt/svgbobdoc/compare/0.2.0...0.2.1
[0.2.0]: https://github.com/yvt/svgbobdoc/compare/0.1.0...0.2.0
