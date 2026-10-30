# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [11.2.0](https://github.com/rust-embedded/aarch64-cpu/compare/v11.1.0...v11.2.0) - 2025-11-29

### Added

- Add VMPIDR_EL2, MDSCR_EL1, MDCR_EL2 (thanks @CUB3D)
- Add missing fields to HCR_EL2 (thanks @CUB3D)
- Add AFSR0_EL1, AFSR1_EL1, CONTEXTIDR_EL1 (thanks @kisum9)
- Add up-to-date enumeration for EC field to ESR_EL1 and ESR_EL2 (thanks @kisum9)

### Changed

- Improve registers documentation

## [11.1.0](https://github.com/rust-embedded/aarch64-cpu/compare/v11.0.0...v11.1.0) - 2025-10-19

### Added

- Add TCR2_EL1 register
- Add AMAIR_EL1 register
- Add more fields to HCR_EL2

### Changed

- Fix register documentation

## [11.0.0](https://github.com/rust-embedded/aarch64-cpu/compare/v10.0.0...v11.0.0) - 2025-10-12

### Breaking changes

Major version bump due to tock-registers dependency - updated to 0.10

### Added

- Add stackpointer registers SP_EL2 and SP_EL3
- Add hypervisor register support (#41)

### Fixed

- Update HCR_EL2 reorder TSC and TID3 correctly

## [v10.0.0] - 2024-10-26

### Breaking

Major version bump due to tock-registers dependency - updated to 0.9 (#26)

### Added

- Add automatic release pipeline (#30)
- Re-export `tock-registers::interfaces::ReadWriteable` (#23)

- Add register `CNTHP_CTL_EL2` (#24) - "Control register for the EL2 physical timer"
- Add `EL3h` and `EL3t` fields to register `SPSR_EL3` (#28)
- Add registers `CNTPOFF_EL2`, `CPTR_EL2`, `HPFAR_EL2`, `ICC_CTLR_EL1`, `ICC_SRE_EL2`, `ICH_AP0R_EL2`, `ICH_AP1R_EL2`, `ICH_HCR_EL2`, `ICH_LR_EL2`, `ICH_MISR_EL2`, `ICH_VMCR_EL2`, `ICH_VTR_EL2`, `ID_AA64AFR0_EL1`, `ID_AA64AFR1_EL1`, `ID_AA64DFR0_EL1`, `ID_AA64DFR1_EL1`, `ID_AA64ISAR1_EL1`, `ID_AA64PFR0_EL1`, `ID_AA64PFR1_EL1` (#27)
- Add fields `TERR`, `TLOR`, `TSW`, `TACR`, `TIDCP`, `TID3`, `BSU`, `FB` to register `HCR_EL2` (#27)
- Add fields to register `ICH_LR0_EL2` (#27)
- Add field `EOS` to register `SCTLR_EL2` (#27)
- Add fields `NSA` and `SL0` to register `VTCR_EL2` (#27)

### Fixed

- Fix writing ESL_EL1 with register bitfield instead of u64 (#27)

## [v9.4.0] - 2023-09-19

Minor version bump due to re-export of tock-registers dependency (#20)

### Added

- Add register `FAR_EL3` (#11)
- Add register `ESR_EL3` (#10)
- Add register `SCTLR_EL3` (#9)
- Add field `TSC` to register `HCR_EL2` (#17)
- Add register `CNTKCTL_EL1` (#12)
- Add registers `APDAKEYHI_EL1`, `APDAKEYLO_EL1`, `APDBKEYHI_EL1`, `APDBKEYLO_EL1`, `APGAKEYHI_EL1`, `APGAKEYLO_EL1`, `APIAKEYHI_EL1`, `APIAKEYLO_EL1`, `APIBKEYHI_EL1`, `APIBKEYLO_EL1` (#14)
- Add registers `RVBAR_EL1`, `RVBAR_EL2`, `RVBAR_EL3` (#8)
- Add registers `MPIDR_EL1` (#6)
- Add registers `TPIDR_EL2` (#7)

### Fixed

- Fix bitwidth of field `BADDR` of register `VTTBR_EL2` (#18)

### Changed

- Re-export of tock-registers dependency (#20)
- Enable write to registers `ESR_EL1` and `ESR_EL2` (#15)

[Unreleased]: https://github.com/rust-embedded/aarch64-cpu/compare/v9.4.0...HEAD
[v9.4.0]: https://github.com/rust-embedded/aarch64-cpu/compare/v9.3.1...v9.4.0
