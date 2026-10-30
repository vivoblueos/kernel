# Changelog

All future notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

Due to the CHANGELOG file being neglected it has been updated to only reflect changes for versions 3.0.0 and above.
Git tags have still been added to reflect the state of the code for each version. The only version missing is 2.2.1 which
isn't in git history.

## [Unreleased]
### Changed
- CHANGELOG changed to start at 3.0.0. With past versions referenced with git tags except 2.2.1.
- FTPS can now be done with [native-tls](https://crates.io/crates/native-tls) or [openssl](https://crates.io/crates/openssl) libraries. This creates better support for macOS and Windows. By default openssl is still used when just the `secure` flag is given. To use `native-tls` use the `secure` flag with the `native-tls` flag.
- The `connect` function now returns the welcome message of the server.

## [3.0.1] - 2018-04-15
### Added
- 200 as a proper response code for CDUP.

## [3.0.0] - 2018-02-28

* Start of CHANGELOG

[Unreleased]: https://github.com/mattnenterprise/rust-ftp/compare/v3.0.1...HEAD
[3.0.1]: https://github.com/mattnenterprise/rust-ftp/compare/v3.0.0...v3.0.1
[3.0.0]: https://github.com/mattnenterprise/rust-ftp/compare/v2.1.2...v3.0.0

## Previous Releases
2.2.1: Unknown - Couldn't find version reference in the codebase.

2.1.2: https://github.com/mattnenterprise/rust-ftp/compare/v2.1.1...v2.1.2

2.1.1: https://github.com/mattnenterprise/rust-ftp/compare/v2.0.1...v2.1.1

2.0.1: https://github.com/mattnenterprise/rust-ftp/compare/v2.0.0...v2.0.1

2.0.0: https://github.com/mattnenterprise/rust-ftp/compare/v1.0.0...v2.0.0

1.0.0: https://github.com/mattnenterprise/rust-ftp/compare/v0.0.8...v1.0.0

0.0.8: https://github.com/mattnenterprise/rust-ftp/compare/v0.0.7...v0.0.8

0.0.7: https://github.com/mattnenterprise/rust-ftp/compare/ef996f0...v0.0.7
