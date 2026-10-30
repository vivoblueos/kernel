# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

## [Unreleased]

## [v0.10.0] - 2026-02-17

### Added

- added `SpiInterface::release`
- added `RM67162` model support
- made `InitError` visible
- added `ILI9488` model support
- added `ILI9228` model support
- added `KIND` constant to `Interface` trait to detect invalid model, color format, and interface combinations
- added `InvalidConfiguration` variant to `InitError` enum
- added `update_address_window` in Model trait.
- added feature-gated defmt support for Interface errors.

### Changed

- changed the returned error type of `Model::init` to a new `ModelInitError` type to allow implementations to report configuration errors
- added new errors returned from `Builder::init` in case of invalid `display_size` or `display_offset` parameters
- Move functions `set_vertical_scroll_offset`, `set_vertical_scroll_region`, `set_tearing_effect`, `update_options`, `software_reset`, `write_memory_start`, `wake` and `sleep` 's dcs command part into Model trait from Display trait.

## Removed

- remove unused `nb` dependency
- remove panic from `Builder::display_size` if invalid size is given

## [v0.9.0] - 2025-01-10

### Added

- added `GC9107` model support

### Changed

- replaced `display_interface` with our own trait and implementations for significantly better performance, see the [migration guide](https://github.com/almindor/mipidsi/blob/master/docs/MIGRATION.md#v08---09) for details

## [v0.8.0] - 2024-05-24

### Added

- added `GC9A01` model support
- added `Display::wake` method
- added `Display::sleep` method
- added `Display::is_sleeping` method
- added `Display::dcs` method to allow sending custom DCS commands to the device
- added `TestImage::default`
- added `ST7796` model support (#125)

### Changed

- rename all `Builder::with_*` methods to versions without the `with_` prefix to conform to the Rust API guidelines. See [this issue](https://github.com/almindor/mipidsi/issues/113) for more info
- `options` and `error` submodule types are no longer re-exported from the main library
- DCS commands param fields are now all consistently private with added constructors for all such commands
- DCS command constructors (such as `SetAddressMode::new`) are now marked as `const`, so DCS commands can be constructed in
  [const contexts](https://doc.rust-lang.org/reference/const_eval.html#const-context)
- replaced `window_offset_handler` function pointer with `offset` field
- default to disabled color inversion for all generic models
- renamed `Display::set_scroll_region` and `Display::set_scroll_offset` into `set_vertical_scroll_region` and `set_vertical_scroll_offset`
- updated to `embedded-hal v1.0.0`
- updated to `display-interface v0.5.0`
- removed `Model::default_options`
- bumped MSRV to `v1.75`
- fixed `DrawTarget::fill_contiguous` for images that overlap the edge of the framebuffer
- replaced model specific `Builder` constructors (like `Builder::gc9a01`) with one generic `Builder::new` constructor
- replaced rest pin parameter in `Builder::init` by `Builder::with_reset_pin` setter
- removed setters and getters from `ModelOptions` and instead made the fields public
- added `non_exhaustive` attribute to `ModelOptions`
- added checks to `Builder::init` to ensure that the display size and display offset are valid

### Removed

- removed `Builder::with_framebuffer_size`

## [v0.7.1] - 2023-05-24

### Changed

- fixed MSRV in `Cargo.toml` to match the rest at `v1.61`

## [v0.7.0] - 2023-05-24

### Changed

- switched `embedded-graphics-core v0.4.0`
- updated initialization delays `ILI934x` model

## [v0.6.0] - 2023-01-12

### Added

- added `Builder::with_window_offset_handler` method
- added `ModelOptions::invert_colors` flag
- added `Builder::with_invert_colors(bool)` method
- added `ILI9341` model support

### Changed

- `Model::init` changed to expect `options: &ModelOptions`
- reworked how `DCS` instructions are handled using the new `dcs` module and `DcsCommand` trait and implementations
- reworked model init functions to use new `dcs` module

### Removed

- removed duplicated `INVON` call in `ST7735s` model init

## [v0.5.0] - 2022-10-19

### Added

- added the `Builder` as construction method for displays to simplify configuration
  and protect against use-before-init bugs
- added `Model::default_options()` so that each model can provide a sane default regardless of helper constructors

### Changed

- `Model` no longer has to own `ModelOptions`
- `Model::new` was removed
- the optional `RST` reset hw pin is now only used during the `Builder::init` call

### Removed

- removed direct `Display` constructors. Use `Builder` instead (see migration guide)
- removed `DisplayOptions` in favour of `Builder` settings

## [v0.4.0] - 2022-09-30

### Added

- support for model variants via `DisplayOptions`
- support for `raspberry pico1` variant of the `ST7789` display
- support for the `waveshare` variants of the `ST7789` display

### Changed

- split [DisplayOptions] into [DisplayOptions] and [ModelOptions] with sizing initialization safety constructors
- refactored `Display::init` and constructors to match new variant code
- fixed off by one error in fill operations

### Removed

- removed "no reset pin" constructor helpers (uses `Option` now)

## [v0.3.0] - 2022-08-30

### Added

- added `ILI9342C` model support thanks to [Jesse Braham's](https://github.com/jessebraham) [PR](https://github.com/almindor/mipidsi/pull/25)

## [v0.2.2] - 2022-08-26

### Changed

- fix `Display::clear` out of bounds pixels
- remove `ST7789` model `Bgr` bit override

## [v0.2.1] - 2022-08-03

### Added

- clarified display model constructor usage in `README`

### Changed

- fix `i32` -> `u16` conversion overflow bug in `batch` module in case of negative coordinates

## [v0.2.0] - 2021-04-12

### Changed

- fix RGB/BGR color issue on some models
- expand `Orientation` to use mirror image settings properly
- change `Display::init` to include `DisplayOptions` and allow setting all `MADCTL` values on init, including `Orientation`
- fix issues [#6](https://github.com/almindor/mipidsi/issues/6), [#8](https://github.com/almindor/mipidsi/issues/8) and [#10](https://github.com/almindor/mipidsi/issues/10)
  - big thanks to [@brianmay](https://github.com/brianmay) and [@KerryRJ](https://github.com/KerryRJ)

## [v0.1.0] - 2021-09-09

### Added

- Initial release
