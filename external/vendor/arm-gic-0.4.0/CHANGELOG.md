# Changelog

## 0.4.0

### Breaking changes

- Changed `GicV3::new` to take flag indicating whether GIC is v3 or v4, rather than GICR stride.
- Added new `gicv3::registers::GicrType` bitflags type and used it for `Gicr.typer` register field.

### Improvements

- Made `GicV3::gicd_barrier` public.

## 0.3.0

### Breaking changes

- Added `AlreadyAsleep` variant to `GICRError` enum.
- Changed `GicV3::gicd_ptr`, `GicV3::gicr_ptr` and `GicV3::sgi_ptr` to return a `UniqueMmioPointer`.
- `GicV2` and `GicV3` now have a lifetime parameter, indicating the lifetime for which the driver
  has exclusive access to the MMIO regions of the GIC.
- `GicV2::new` and `GicV3::new` now take pointers to register struct types rather than `*mut u64`.

### Improvements

- Made `IntId::is_sgi` public.
- Made `IntId::is_*` methods const.
- Added `GicV3::redistributor_mark_core_asleep` method.
- Made `gicv2::registers` public.

## 0.2.2

### Improvements

- Added `fakes` feature which causes all system register access to be redirected to a fake instead.
  This can be useful for tests.

## 0.2.1

### Bugfixes

- Fixed docs.rs build.

## 0.2.0

### Breaking changes

- `IntId` and `Trigger` moved to top-level module, as they are shared with GICv2 driver.
- Added support for multiple cores. `GicV3::new` now takes the CPU count and redistributor stride,
  and various other method take a cpu index.

### Bugfixes

- Fixed `GicV3::setup` not to write to GICD IGROUPR[0].
- Fixed `GicV3::enable_interrupt` not to write to GICD for private interrupt IDs.
- Return `None` from `get_and_acknowledge_interrupt` for `SPECIAL_NONE`.

### Improvements

- Added more interrupt types to `IntId`, and public constants for number of each type.
- Added constants to `IntId` for special interrupt IDs.
- Added methods to read type register and its fields.
- Added `set_group`, `redistributor_mark_core_awake` and other methods to `GicV3`.
- Added support for GICv2 in a separate `GicV2` driver.
- Added support for aarch32.

## 0.1.2

### Bugfixes

- Changed `irouter` and `irouter_e` fields of `GICD` to use u64, to match GIC specification.

### Improvements

- Made `gicv3::registers` module public and added methods to `GicV3` to get pointers to registers.

## 0.1.1

### Improvements

- Implemented `Send` and `Sync` for `GicV3`.

## 0.1.0

Initial version, with basic support for GICv3 (and 4) on aarch64.
