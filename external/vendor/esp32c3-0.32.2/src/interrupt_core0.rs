#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    core_0_intr_map: [CORE_0_INTR_MAP; 62],
    core_0_intr_status: [CORE_0_INTR_STATUS; 2],
    clock_gate: CLOCK_GATE,
    cpu_int_enable: CPU_INT_ENABLE,
    cpu_int_type: CPU_INT_TYPE,
    cpu_int_clear: CPU_INT_CLEAR,
    cpu_int_eip_status: CPU_INT_EIP_STATUS,
    cpu_int_pri: [CPU_INT_PRI; 32],
    cpu_int_thresh: CPU_INT_THRESH,
    _reserved9: [u8; 0x0664],
    interrupt_reg_date: INTERRUPT_REG_DATE,
}
impl RegisterBlock {
    #[doc = "0x00..0xf8 - "]
    #[inline(always)]
    pub const fn core_0_intr_map(&self, n: usize) -> &CORE_0_INTR_MAP {
        &self.core_0_intr_map[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x00..0xf8 - "]
    #[inline(always)]
    pub fn core_0_intr_map_iter(&self) -> impl Iterator<Item = &CORE_0_INTR_MAP> {
        self.core_0_intr_map.iter()
    }
    #[doc = "0xf8..0x100 - mac intr map register"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is the index of register in the array. `n == 0` corresponds to `CORE_0_INTR_STATUSREG_0` register.</div>"]
    #[inline(always)]
    pub const fn core_0_intr_status(&self, n: usize) -> &CORE_0_INTR_STATUS {
        &self.core_0_intr_status[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0xf8..0x100 - mac intr map register"]
    #[inline(always)]
    pub fn core_0_intr_status_iter(&self) -> impl Iterator<Item = &CORE_0_INTR_STATUS> {
        self.core_0_intr_status.iter()
    }
    #[doc = "0xf8 - mac intr map register"]
    #[inline(always)]
    pub const fn core_0_intr_statusreg_0(&self) -> &CORE_0_INTR_STATUS {
        self.core_0_intr_status(0)
    }
    #[doc = "0xfc - mac intr map register"]
    #[inline(always)]
    pub const fn core_0_intr_statusreg_1(&self) -> &CORE_0_INTR_STATUS {
        self.core_0_intr_status(1)
    }
    #[doc = "0x100 - mac intr map register"]
    #[inline(always)]
    pub const fn clock_gate(&self) -> &CLOCK_GATE {
        &self.clock_gate
    }
    #[doc = "0x104 - mac intr map register"]
    #[inline(always)]
    pub const fn cpu_int_enable(&self) -> &CPU_INT_ENABLE {
        &self.cpu_int_enable
    }
    #[doc = "0x108 - mac intr map register"]
    #[inline(always)]
    pub const fn cpu_int_type(&self) -> &CPU_INT_TYPE {
        &self.cpu_int_type
    }
    #[doc = "0x10c - mac intr map register"]
    #[inline(always)]
    pub const fn cpu_int_clear(&self) -> &CPU_INT_CLEAR {
        &self.cpu_int_clear
    }
    #[doc = "0x110 - mac intr map register"]
    #[inline(always)]
    pub const fn cpu_int_eip_status(&self) -> &CPU_INT_EIP_STATUS {
        &self.cpu_int_eip_status
    }
    #[doc = "0x114..0x194 - mac intr map register"]
    #[inline(always)]
    pub const fn cpu_int_pri(&self, n: usize) -> &CPU_INT_PRI {
        &self.cpu_int_pri[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x114..0x194 - mac intr map register"]
    #[inline(always)]
    pub fn cpu_int_pri_iter(&self) -> impl Iterator<Item = &CPU_INT_PRI> {
        self.cpu_int_pri.iter()
    }
    #[doc = "0x194 - mac intr map register"]
    #[inline(always)]
    pub const fn cpu_int_thresh(&self) -> &CPU_INT_THRESH {
        &self.cpu_int_thresh
    }
    #[doc = "0x7fc - mac intr map register"]
    #[inline(always)]
    pub const fn interrupt_reg_date(&self) -> &INTERRUPT_REG_DATE {
        &self.interrupt_reg_date
    }
}
#[doc = "CORE_0_INTR_MAP (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_intr_map::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_intr_map::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_intr_map`] module"]
pub type CORE_0_INTR_MAP = crate::Reg<core_0_intr_map::CORE_0_INTR_MAP_SPEC>;
#[doc = ""]
pub mod core_0_intr_map;
#[doc = "CORE_0_INTR_STATUS (r) register accessor: mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_intr_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_intr_status`] module"]
pub type CORE_0_INTR_STATUS = crate::Reg<core_0_intr_status::CORE_0_INTR_STATUS_SPEC>;
#[doc = "mac intr map register"]
pub mod core_0_intr_status;
#[doc = "CLOCK_GATE (rw) register accessor: mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`clock_gate::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clock_gate::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clock_gate`] module"]
pub type CLOCK_GATE = crate::Reg<clock_gate::CLOCK_GATE_SPEC>;
#[doc = "mac intr map register"]
pub mod clock_gate;
#[doc = "CPU_INT_ENABLE (rw) register accessor: mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_int_enable::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_int_enable::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_int_enable`] module"]
pub type CPU_INT_ENABLE = crate::Reg<cpu_int_enable::CPU_INT_ENABLE_SPEC>;
#[doc = "mac intr map register"]
pub mod cpu_int_enable;
#[doc = "CPU_INT_TYPE (rw) register accessor: mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_int_type::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_int_type::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_int_type`] module"]
pub type CPU_INT_TYPE = crate::Reg<cpu_int_type::CPU_INT_TYPE_SPEC>;
#[doc = "mac intr map register"]
pub mod cpu_int_type;
#[doc = "CPU_INT_CLEAR (rw) register accessor: mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_int_clear::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_int_clear::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_int_clear`] module"]
pub type CPU_INT_CLEAR = crate::Reg<cpu_int_clear::CPU_INT_CLEAR_SPEC>;
#[doc = "mac intr map register"]
pub mod cpu_int_clear;
#[doc = "CPU_INT_EIP_STATUS (r) register accessor: mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_int_eip_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_int_eip_status`] module"]
pub type CPU_INT_EIP_STATUS = crate::Reg<cpu_int_eip_status::CPU_INT_EIP_STATUS_SPEC>;
#[doc = "mac intr map register"]
pub mod cpu_int_eip_status;
#[doc = "CPU_INT_PRI (rw) register accessor: mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_int_pri::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_int_pri::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_int_pri`] module"]
pub type CPU_INT_PRI = crate::Reg<cpu_int_pri::CPU_INT_PRI_SPEC>;
#[doc = "mac intr map register"]
pub mod cpu_int_pri;
#[doc = "CPU_INT_THRESH (rw) register accessor: mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_int_thresh::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_int_thresh::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_int_thresh`] module"]
pub type CPU_INT_THRESH = crate::Reg<cpu_int_thresh::CPU_INT_THRESH_SPEC>;
#[doc = "mac intr map register"]
pub mod cpu_int_thresh;
pub use crate::aes::{date as interrupt_reg_date, DATE as INTERRUPT_REG_DATE};
