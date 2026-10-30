# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

<!-- next-header -->

## [Unreleased] - ReleaseDate

## [0.1.3] - 2026-01-26

- Work around `unused_assignment` warning

## [0.1.2] - 2026-01-12

- Fixed: disabling the `std` feature flag now marks the crate as `no_std`

# [0.1.1] - 2024-02-27

## Added

## Changed

## Fixed

- Fixed an issue where some multi-line doc strings containing placeholders did not compile

# [0.1.0] - 2024-02-26

## Added

- Forked off of `displaydoc`
- `{}` placeholders can now contain arbitrary expressions. The first identifier refers to a struct/enum variant field
- Multi-line doc comments are now collected, except when disabled with `#[ignore_extra_doc_attributes]`
- `#[ignore_extra_doc_attributes]` can now be placed on top of any field where doc comments are expected

## Changed

- Renamed `#[displaydoc()]` to `#[display()]`
