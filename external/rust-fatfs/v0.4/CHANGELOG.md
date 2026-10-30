Changelog
=========

0.4.0 (not released yet)
------------------------
New features:
* Add `fatfs::Read`, `fatfs::Write` and `fatfs::Seek` traits and use them to replace usages of `Read`, `Write`, `Seek`
  traits from `std::io` (BREAKING CHANGE). New traits are subtraits of `fatfs::IoBase` and use `IoBase::Error`
  associated type for errors.
* Add `Error` enum and use it to replace all usages of `std::io::Error` struct (BREAKING CHANGE). The new enum items
  allow better differentiation of errors than `std::io::ErrorKind`.
* Implement `From<Error<std::io::Error>>` trait for `std::io::Error` to simplify errors conversion.
* Implement `Read`, `Write`, `Seek` traits from `std::io` for `fatfs::File` struct.
* Add `StdIoWrapper` struct that implements newly added `Read`, `Write`, `Seek` traits and wraps types that implement
  corresponding traits from `std::io` module.
* Add `IntoStorage` trait and implement it for types that implement `Read`, `Write`, `Seek` traits from `std::io` and
  types that implement newly added `Read`, `Write`, `Seek` traits from this crate. Make `FileSystem::new` accept types
  that implement `IntoStorage`.
* Remove `core_io` dependency. There are no Rust compiler restrictions for `no_std` builds anymore.
* Add type parameters for `TimeProvider` and `OemCpConverter` in `FileSystem`, `File`, `Dir`, `DirEntry`, `FsOptions`
  public structs and require an owned time provider and oem CP converter instead of a reference with a static lifetime in
  `FsOptions` (BREAKING CHANGE). This change allows `FileSystem` usage in multi-threaded environment (e.g. wrapped in a
  `Mutex`).
* Add non-public field to `Date`, `Time`, `DateTime` structures to disallow direct instantiation (BREAKING CHANGE).
* Add `Date::new`, `Time::new`, `DateTime::new` functions that instiantiate corresponding structures after ensuring
  that arguments are in the supported range. They panic if this is not the case.
* Fix time encoding during a leap second if using `chrono`.
* Create directory entry with `VOLUME_ID` attribute when formatting if volume label was set in `FormatVolumeOptions`.
* Fix creating directory entries when `lfn` feature is enabled and `alloc` feature is disabled
* Fix `format_volume` function panicking in debug build for FAT12 volumes with size below 1 MB
* Fix index out of range panic when reading 248+ characters long file names with `alloc` feature disabled
* Remove `byteorder` dependency.
* Bump up minimal Rust compiler version to 1.65.0.
* Build the crate using the 2021 edition.
* Add support for compile-time configuration of logging levels via Cargo features. By default, all logging levels are
  enabled, including "trace" and up.
* Disable chrono default features except `clock`
* Use chrono naive types instead of deprecated `chrono::Date` (BREAKING CHANGE)
* Add defaults for `FileSystem` generic parameters: `TP = DefaultTimeProvider`, `OCC = LossyOemCpConverter`
* Structures `FsOptions`, `ChronoTimeProvider`, `NullTimeProvider` and `LossyOemCpConverter` now implement `Default` trait
* Undeprecate `set_created`, `set_accessed`, `set_modified` methods on `File` - there are scenarios where those methods are needed
* Relax BPB validation by allowing non-zero values in both `total_sectors_32` and `total_sectors_16`
* Add `strict` field in `FsOptions`, which allows disabling validation of boot signature to improve compatibility with old FAT images

Bug fixes:
* Fix formatting volumes with size in range 4096-4199 KB
* Always respect `fat_type` from `FormatVolumeOptions`
* Fill FAT32 root directory clusters with zeros after allocation to avoid interpreting old data as directory entries
* Put '.' and '..' in the first two directory entries. (fixes "Expected a valid '.' entry in this slot." fsck error)
* Set the cluster number to 0 in the ".." directory entry if it points to the root dir

0.3.4 (2020-07-20)
------------------
Bug fixes:
* Fix time encoding and decoding in a directory entry.

0.3.3 (2019-11-10)
------------------
Bug fixes:
* Add missing characters to the whitelist for long file name (`^`, `#`, `&`)
* Fix invalid short file names for `.` and `..` entries when creating a new directory
* Fix `no_std` build

Misc changes:
* Fix compiler warnings
* Improve documentation

0.3.2 (2018-12-29)
------------------
New features:
* Add `format_volume` function for initializing a FAT filesystem on a partition
* Add more checks of filesystem correctness when mounting

Bug fixes:
* Clear directory returned from `create_dir` method - upgrade ASAP if this method is used
* Fix handling of FSInfo sector on FAT32 volumes with sector size different than 512 - upgrade ASAP if such sector size is used
* Use `write_all` in `serialize` method for FSInfo sector - previously it could have been improperly updated

0.3.1 (2018-10-20)
------------------
New features:
* Increased file creation time resolution from 2s to 1/100s
* Added oem_cp_converter filesystem option allowing to provide custom short name decoder
* Added time_provider filesystem option allowing to provide time used when modifying directory entries
* Added marking volume as dirty on first write and not-dirty on unmount
* Added support for reading volume label from root directory

Bug fixes:
* Fixed handling of short names with spaces in the middle - all characters after first space in 8.3 components were
  stripped before
* Fixed decoding 0xE5 character in first byte of short name - if first character of short name is equal to 0xE5,
  it was read as 0x05
* Preserve 4 most significant bits in FAT32 entries - it is required by FAT specification, but previous behavior
  should not cause any compatibility problem because all known implementations ignore those bits
* Fixed warnings for file entries without LFN entries - they were handled properly, but caused warnings in run-time

Misc changes:
* Deprecated set_created. set_accessed, set_modified methods on File - those fields are updated automatically using
  information provided by TimeProvider
* Fixed size formatting in ls.rs example
* Added more filesystem checks causing errors or warnings when incompatibility is detected
* Removed unnecessary clone() calls
* Code formatting and docs fixes
