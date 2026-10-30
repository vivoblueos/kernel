// Copyright 2023 The arm-gic Authors.
// This project is dual-licensed under Apache 2.0 and MIT terms.
// See LICENSE-APACHE and LICENSE-MIT for details.

#[cfg(any(test, feature = "fakes"))]
#[macro_use]
pub mod fake;

#[cfg(all(not(any(test, feature = "fakes")), target_arch = "aarch64"))]
#[macro_use]
mod aarch64;

#[cfg(all(not(any(test, feature = "fakes")), target_arch = "arm"))]
#[macro_use]
mod aarch32;

read_sysreg32!(icc_iar1_el1, 0, c12, c12, 0, read_icc_iar1_el1);

write_sysreg32!(icc_ctlr_el1, 0, c12, c12, 4, write_icc_ctlr_el1);
write_sysreg32!(icc_eoir1_el1, 0, c12, c12, 1, write_icc_eoir1_el1);
write_sysreg32!(icc_igrpen0_el1, 0, c12, c12, 6, write_icc_igrpen0_el1);
write_sysreg32!(icc_igrpen1_el1, 0, c12, c12, 7, write_icc_igrpen1_el1);
write_sysreg32!(icc_pmr_el1, 0, c4, c6, 0, write_icc_pmr_el1);
write_sysreg64!(icc_sgi1r_el1, 0, c12, write_icc_sgi1r_el1);
write_sysreg32!(icc_sre_el1, 0, c12, c12, 5, write_icc_sre_el1);
