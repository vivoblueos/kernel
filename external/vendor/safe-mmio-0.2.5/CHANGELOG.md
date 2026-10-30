# Changelog

## 0.2.5

### Improvements

- Added `UniqueMmioPointer::take` for arrays and slices, similar to `get` but taking ownership of
  the original pointer rather than borrowing it.
- Added implementation of `From` to convert from pointer to array to array of pointers.
- Implemented `Copy` for `SharedMmioPointer`.
- Extended lifetimes of values returned from `SharedMmioPointer::as_slice`,
  `SharedMmioPointer::get`, `SharedMmioPointer::split` and `field_shared!`. They are now tied only
  to the lifetime parameter of the original `SharedMmioPointer`, not the lifetime of the reference.

## 0.2.4

### Improvements

- Added `UniqueMmioPointer::as_mut_slice` and `SharedMmioPointer::as_slice` to convert from array
  pointer to slice pointer.
- Added implementations of `From` to convert from array pointers to slice pointers.
- Added implementations of `From` to convert from pointers to `T` to pointers to `[T; 1]` or `[T]`.
- Added `split_fields!` macro to split a `UniqueMmioPointer` to a struct into several
  `UniqueMmioPointer`s to its fields.

## 0.2.3

### Improvements

- Made many methods `const`, in particular:
  - `PhysicalInstance::new`
  - `PhysicalInstance::pa`
  - `SharedMmioPointer::child`
  - `SharedMmioPointer::get`
  - `SharedMmioPointer::new`
  - `SharedMmioPointer::ptr`
  - `UniqueMmioPointer::child`
  - `UniqueMmioPointer::get`
  - `UniqueMmioPointer::new`
  - `UniqueMmioPointer::ptr_mut`
  - `UniqueMmioPointer::ptr_nonnull`
- Fixed `field!` and `field_shared!` to allow getting unsized fields (e.g. slices) of structs.
- Added `UniqueMmioPointer::reborrow`.

## 0.2.2

### Bugfixes

- Implemented `KnownLayout` for `ReadPureWrite`. This was missed accidentally before.

## 0.2.1

### New features

- Added `get` method to `UniqueMmioPointer<[T; N]>` and `SharedMmioPointer<[T; N]>`.

## 0.2.0

### Breaking changes

- Renamed `OwnedMmioPointer` to `UniqueMmioPointer`.

### New features

- Added `SharedMmioPointer` for an MMIO pointer that is not necessarily unique. Unlike a
  `UniqueMmioPointer`, a `SharedMmioPointer` can be cloned. `UniqueMmioPointer` derefs to
  `SharedMmioPointer` and can also be converted to it.
- Added `get` and `split` methods on `UniqueMmioPointer<[T]>` and `UniqueMmioPointer<[T; _]>`
  respectively, to go from a pointer to a slice or field to pointers to the individual elements.
- Added `field!` and `field_shared!` macros to go from a pointer to a struct to a pointer to an
  individual field.
- Added `write_unsafe` and `read_unsafe` methods on `UniqueMmioPointer` and `SharedMmioPointer`.
  These call `write_volatile` and `read_volatile` on most platforms, but on aarch64 are implemented
  with inline assembly instead to work around
  [a bug with how volatile writes and reads are implemented](https://github.com/rust-lang/rust/issues/131894).
- Added wrapper types `ReadOnly`, `ReadPure`, `WriteOnly`, `ReadWrite` and `ReadPureWrite` to
  indicate whether a field can safely be written or read (with or without side-effects). Added safe
  `write` and `read` methods on `UniqueMmioPointer` or `SharedMmioPointer` for these.

## 0.1.0

Initial release.
