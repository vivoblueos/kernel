#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster CPU%s, containing CORE_?_DEBUG_MODE, CORE_?_AREA_DRAM0_0_MAX, CORE_?_AREA_DRAM0_0_MIN, CORE_?_AREA_DRAM0_1_MAX, CORE_?_AREA_DRAM0_1_MIN, CORE_?_AREA_PC, CORE_?_AREA_PIF_0_MAX, CORE_?_AREA_PIF_0_MIN, CORE_?_AREA_PIF_1_MAX, CORE_?_AREA_PIF_1_MIN, CORE_?_AREA_SP, CORE_?_DRAM0_EXCEPTION_MONITOR_0, CORE_?_DRAM0_EXCEPTION_MONITOR_1, CORE_?_DRAM0_EXCEPTION_MONITOR_2, CORE_?_DRAM0_EXCEPTION_MONITOR_3, CORE_?_INTR_CLR, CORE_?_INTR_ENA, CORE_?_INTR_RAW, CORE_?_IRAM0_EXCEPTION_MONITOR_0, CORE_?_IRAM0_EXCEPTION_MONITOR_1, CORE_?_LASTPC_BEFORE_EXCEPTION, CORE_?_MONTR_ENA, CORE_?_RCD_EN, CORE_?_RCD_PDEBUGPC, CORE_?_RCD_PDEBUGSP, CORE_?_SP_MAX, CORE_?_SP_MIN, CORE_?_SP_PC"]
pub struct CPU {
    montr_ena: MONTR_ENA,
    intr_raw: INTR_RAW,
    intr_ena: INTR_ENA,
    intr_clr: INTR_CLR,
    area_dram0_0_min: AREA_DRAM0_0_MIN,
    area_dram0_0_max: AREA_DRAM0_0_MAX,
    area_dram0_1_min: AREA_DRAM0_1_MIN,
    area_dram0_1_max: AREA_DRAM0_1_MAX,
    area_pif_0_min: AREA_PIF_0_MIN,
    area_pif_0_max: AREA_PIF_0_MAX,
    area_pif_1_min: AREA_PIF_1_MIN,
    area_pif_1_max: AREA_PIF_1_MAX,
    area_pc: AREA_PC,
    area_sp: AREA_SP,
    sp_min: SP_MIN,
    sp_max: SP_MAX,
    sp_pc: SP_PC,
    rcd_en: RCD_EN,
    rcd_pdebugpc: RCD_PDEBUGPC,
    rcd_pdebugsp: RCD_PDEBUGSP,
    iram0_exception_monitor_0: IRAM0_EXCEPTION_MONITOR_0,
    iram0_exception_monitor_1: IRAM0_EXCEPTION_MONITOR_1,
    dram0_exception_monitor_0: DRAM0_EXCEPTION_MONITOR_0,
    dram0_exception_monitor_1: DRAM0_EXCEPTION_MONITOR_1,
    dram0_exception_monitor_2: DRAM0_EXCEPTION_MONITOR_2,
    dram0_exception_monitor_3: DRAM0_EXCEPTION_MONITOR_3,
    _reserved26: [u8; 0x08],
    lastpc_before_exception: LASTPC_BEFORE_EXCEPTION,
    debug_mode: DEBUG_MODE,
    _reserved_end: [u8; 0x24],
}
impl CPU {
    #[doc = "0x00 - ASSIST_DEBUG_CORE_0_MONTR_ENA_REG"]
    #[inline(always)]
    pub const fn montr_ena(&self) -> &MONTR_ENA {
        &self.montr_ena
    }
    #[doc = "0x04 - core0 monitor interrupt status register"]
    #[inline(always)]
    pub const fn intr_raw(&self) -> &INTR_RAW {
        &self.intr_raw
    }
    #[doc = "0x08 - core0 monitor interrupt enable register"]
    #[inline(always)]
    pub const fn intr_ena(&self) -> &INTR_ENA {
        &self.intr_ena
    }
    #[doc = "0x0c - core0 monitor interrupt clr register"]
    #[inline(always)]
    pub const fn intr_clr(&self) -> &INTR_CLR {
        &self.intr_clr
    }
    #[doc = "0x10 - core0 dram0 region0 addr configuration register"]
    #[inline(always)]
    pub const fn area_dram0_0_min(&self) -> &AREA_DRAM0_0_MIN {
        &self.area_dram0_0_min
    }
    #[doc = "0x14 - core0 dram0 region0 addr configuration register"]
    #[inline(always)]
    pub const fn area_dram0_0_max(&self) -> &AREA_DRAM0_0_MAX {
        &self.area_dram0_0_max
    }
    #[doc = "0x18 - core0 dram0 region1 addr configuration register"]
    #[inline(always)]
    pub const fn area_dram0_1_min(&self) -> &AREA_DRAM0_1_MIN {
        &self.area_dram0_1_min
    }
    #[doc = "0x1c - core0 dram0 region1 addr configuration register"]
    #[inline(always)]
    pub const fn area_dram0_1_max(&self) -> &AREA_DRAM0_1_MAX {
        &self.area_dram0_1_max
    }
    #[doc = "0x20 - core0 PIF region0 addr configuration register"]
    #[inline(always)]
    pub const fn area_pif_0_min(&self) -> &AREA_PIF_0_MIN {
        &self.area_pif_0_min
    }
    #[doc = "0x24 - core0 PIF region0 addr configuration register"]
    #[inline(always)]
    pub const fn area_pif_0_max(&self) -> &AREA_PIF_0_MAX {
        &self.area_pif_0_max
    }
    #[doc = "0x28 - core0 PIF region1 addr configuration register"]
    #[inline(always)]
    pub const fn area_pif_1_min(&self) -> &AREA_PIF_1_MIN {
        &self.area_pif_1_min
    }
    #[doc = "0x2c - core0 PIF region1 addr configuration register"]
    #[inline(always)]
    pub const fn area_pif_1_max(&self) -> &AREA_PIF_1_MAX {
        &self.area_pif_1_max
    }
    #[doc = "0x30 - core0 area pc status register"]
    #[inline(always)]
    pub const fn area_pc(&self) -> &AREA_PC {
        &self.area_pc
    }
    #[doc = "0x34 - core0 area sp status register"]
    #[inline(always)]
    pub const fn area_sp(&self) -> &AREA_SP {
        &self.area_sp
    }
    #[doc = "0x38 - stack min value"]
    #[inline(always)]
    pub const fn sp_min(&self) -> &SP_MIN {
        &self.sp_min
    }
    #[doc = "0x3c - stack max value"]
    #[inline(always)]
    pub const fn sp_max(&self) -> &SP_MAX {
        &self.sp_max
    }
    #[doc = "0x40 - stack monitor pc status register"]
    #[inline(always)]
    pub const fn sp_pc(&self) -> &SP_PC {
        &self.sp_pc
    }
    #[doc = "0x44 - record enable configuration register"]
    #[inline(always)]
    pub const fn rcd_en(&self) -> &RCD_EN {
        &self.rcd_en
    }
    #[doc = "0x48 - record status regsiter"]
    #[inline(always)]
    pub const fn rcd_pdebugpc(&self) -> &RCD_PDEBUGPC {
        &self.rcd_pdebugpc
    }
    #[doc = "0x4c - record status regsiter"]
    #[inline(always)]
    pub const fn rcd_pdebugsp(&self) -> &RCD_PDEBUGSP {
        &self.rcd_pdebugsp
    }
    #[doc = "0x50 - exception monitor status register0"]
    #[inline(always)]
    pub const fn iram0_exception_monitor_0(&self) -> &IRAM0_EXCEPTION_MONITOR_0 {
        &self.iram0_exception_monitor_0
    }
    #[doc = "0x54 - exception monitor status register1"]
    #[inline(always)]
    pub const fn iram0_exception_monitor_1(&self) -> &IRAM0_EXCEPTION_MONITOR_1 {
        &self.iram0_exception_monitor_1
    }
    #[doc = "0x58 - exception monitor status register2"]
    #[inline(always)]
    pub const fn dram0_exception_monitor_0(&self) -> &DRAM0_EXCEPTION_MONITOR_0 {
        &self.dram0_exception_monitor_0
    }
    #[doc = "0x5c - exception monitor status register3"]
    #[inline(always)]
    pub const fn dram0_exception_monitor_1(&self) -> &DRAM0_EXCEPTION_MONITOR_1 {
        &self.dram0_exception_monitor_1
    }
    #[doc = "0x60 - exception monitor status register4"]
    #[inline(always)]
    pub const fn dram0_exception_monitor_2(&self) -> &DRAM0_EXCEPTION_MONITOR_2 {
        &self.dram0_exception_monitor_2
    }
    #[doc = "0x64 - exception monitor status register5"]
    #[inline(always)]
    pub const fn dram0_exception_monitor_3(&self) -> &DRAM0_EXCEPTION_MONITOR_3 {
        &self.dram0_exception_monitor_3
    }
    #[doc = "0x70 - ASSIST_DEBUG_CORE_0_LASTPC_BEFORE_EXCEPTION"]
    #[inline(always)]
    pub const fn lastpc_before_exception(&self) -> &LASTPC_BEFORE_EXCEPTION {
        &self.lastpc_before_exception
    }
    #[doc = "0x74 - ASSIST_DEBUG_CORE_0_DEBUG_MODE"]
    #[inline(always)]
    pub const fn debug_mode(&self) -> &DEBUG_MODE {
        &self.debug_mode
    }
}
#[doc = "DEBUG_MODE (r) register accessor: ASSIST_DEBUG_CORE_0_DEBUG_MODE\n\nYou can [`read`](crate::Reg::read) this register and get [`debug_mode::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@debug_mode`] module"]
pub type DEBUG_MODE = crate::Reg<debug_mode::DEBUG_MODE_SPEC>;
#[doc = "ASSIST_DEBUG_CORE_0_DEBUG_MODE"]
pub mod debug_mode;
#[doc = "AREA_DRAM0_0_MAX (rw) register accessor: core0 dram0 region0 addr configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`area_dram0_0_max::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`area_dram0_0_max::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@area_dram0_0_max`] module"]
pub type AREA_DRAM0_0_MAX = crate::Reg<area_dram0_0_max::AREA_DRAM0_0_MAX_SPEC>;
#[doc = "core0 dram0 region0 addr configuration register"]
pub mod area_dram0_0_max;
#[doc = "AREA_DRAM0_0_MIN (rw) register accessor: core0 dram0 region0 addr configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`area_dram0_0_min::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`area_dram0_0_min::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@area_dram0_0_min`] module"]
pub type AREA_DRAM0_0_MIN = crate::Reg<area_dram0_0_min::AREA_DRAM0_0_MIN_SPEC>;
#[doc = "core0 dram0 region0 addr configuration register"]
pub mod area_dram0_0_min;
#[doc = "AREA_DRAM0_1_MAX (rw) register accessor: core0 dram0 region1 addr configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`area_dram0_1_max::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`area_dram0_1_max::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@area_dram0_1_max`] module"]
pub type AREA_DRAM0_1_MAX = crate::Reg<area_dram0_1_max::AREA_DRAM0_1_MAX_SPEC>;
#[doc = "core0 dram0 region1 addr configuration register"]
pub mod area_dram0_1_max;
#[doc = "AREA_DRAM0_1_MIN (rw) register accessor: core0 dram0 region1 addr configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`area_dram0_1_min::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`area_dram0_1_min::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@area_dram0_1_min`] module"]
pub type AREA_DRAM0_1_MIN = crate::Reg<area_dram0_1_min::AREA_DRAM0_1_MIN_SPEC>;
#[doc = "core0 dram0 region1 addr configuration register"]
pub mod area_dram0_1_min;
#[doc = "AREA_PC (r) register accessor: core0 area pc status register\n\nYou can [`read`](crate::Reg::read) this register and get [`area_pc::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@area_pc`] module"]
pub type AREA_PC = crate::Reg<area_pc::AREA_PC_SPEC>;
#[doc = "core0 area pc status register"]
pub mod area_pc;
#[doc = "AREA_PIF_0_MAX (rw) register accessor: core0 PIF region0 addr configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`area_pif_0_max::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`area_pif_0_max::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@area_pif_0_max`] module"]
pub type AREA_PIF_0_MAX = crate::Reg<area_pif_0_max::AREA_PIF_0_MAX_SPEC>;
#[doc = "core0 PIF region0 addr configuration register"]
pub mod area_pif_0_max;
#[doc = "AREA_PIF_0_MIN (rw) register accessor: core0 PIF region0 addr configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`area_pif_0_min::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`area_pif_0_min::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@area_pif_0_min`] module"]
pub type AREA_PIF_0_MIN = crate::Reg<area_pif_0_min::AREA_PIF_0_MIN_SPEC>;
#[doc = "core0 PIF region0 addr configuration register"]
pub mod area_pif_0_min;
#[doc = "AREA_PIF_1_MAX (rw) register accessor: core0 PIF region1 addr configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`area_pif_1_max::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`area_pif_1_max::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@area_pif_1_max`] module"]
pub type AREA_PIF_1_MAX = crate::Reg<area_pif_1_max::AREA_PIF_1_MAX_SPEC>;
#[doc = "core0 PIF region1 addr configuration register"]
pub mod area_pif_1_max;
#[doc = "AREA_PIF_1_MIN (rw) register accessor: core0 PIF region1 addr configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`area_pif_1_min::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`area_pif_1_min::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@area_pif_1_min`] module"]
pub type AREA_PIF_1_MIN = crate::Reg<area_pif_1_min::AREA_PIF_1_MIN_SPEC>;
#[doc = "core0 PIF region1 addr configuration register"]
pub mod area_pif_1_min;
#[doc = "AREA_SP (r) register accessor: core0 area sp status register\n\nYou can [`read`](crate::Reg::read) this register and get [`area_sp::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@area_sp`] module"]
pub type AREA_SP = crate::Reg<area_sp::AREA_SP_SPEC>;
#[doc = "core0 area sp status register"]
pub mod area_sp;
#[doc = "DRAM0_EXCEPTION_MONITOR_0 (r) register accessor: exception monitor status register2\n\nYou can [`read`](crate::Reg::read) this register and get [`dram0_exception_monitor_0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dram0_exception_monitor_0`] module"]
pub type DRAM0_EXCEPTION_MONITOR_0 =
    crate::Reg<dram0_exception_monitor_0::DRAM0_EXCEPTION_MONITOR_0_SPEC>;
#[doc = "exception monitor status register2"]
pub mod dram0_exception_monitor_0;
#[doc = "DRAM0_EXCEPTION_MONITOR_1 (r) register accessor: exception monitor status register3\n\nYou can [`read`](crate::Reg::read) this register and get [`dram0_exception_monitor_1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dram0_exception_monitor_1`] module"]
pub type DRAM0_EXCEPTION_MONITOR_1 =
    crate::Reg<dram0_exception_monitor_1::DRAM0_EXCEPTION_MONITOR_1_SPEC>;
#[doc = "exception monitor status register3"]
pub mod dram0_exception_monitor_1;
#[doc = "DRAM0_EXCEPTION_MONITOR_2 (r) register accessor: exception monitor status register4\n\nYou can [`read`](crate::Reg::read) this register and get [`dram0_exception_monitor_2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dram0_exception_monitor_2`] module"]
pub type DRAM0_EXCEPTION_MONITOR_2 =
    crate::Reg<dram0_exception_monitor_2::DRAM0_EXCEPTION_MONITOR_2_SPEC>;
#[doc = "exception monitor status register4"]
pub mod dram0_exception_monitor_2;
#[doc = "DRAM0_EXCEPTION_MONITOR_3 (r) register accessor: exception monitor status register5\n\nYou can [`read`](crate::Reg::read) this register and get [`dram0_exception_monitor_3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dram0_exception_monitor_3`] module"]
pub type DRAM0_EXCEPTION_MONITOR_3 =
    crate::Reg<dram0_exception_monitor_3::DRAM0_EXCEPTION_MONITOR_3_SPEC>;
#[doc = "exception monitor status register5"]
pub mod dram0_exception_monitor_3;
#[doc = "INTR_CLR (w) register accessor: core0 monitor interrupt clr register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`intr_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@intr_clr`] module"]
pub type INTR_CLR = crate::Reg<intr_clr::INTR_CLR_SPEC>;
#[doc = "core0 monitor interrupt clr register"]
pub mod intr_clr;
#[doc = "INTR_ENA (rw) register accessor: core0 monitor interrupt enable register\n\nYou can [`read`](crate::Reg::read) this register and get [`intr_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`intr_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@intr_ena`] module"]
pub type INTR_ENA = crate::Reg<intr_ena::INTR_ENA_SPEC>;
#[doc = "core0 monitor interrupt enable register"]
pub mod intr_ena;
#[doc = "INTR_RAW (r) register accessor: core0 monitor interrupt status register\n\nYou can [`read`](crate::Reg::read) this register and get [`intr_raw::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@intr_raw`] module"]
pub type INTR_RAW = crate::Reg<intr_raw::INTR_RAW_SPEC>;
#[doc = "core0 monitor interrupt status register"]
pub mod intr_raw;
#[doc = "IRAM0_EXCEPTION_MONITOR_0 (r) register accessor: exception monitor status register0\n\nYou can [`read`](crate::Reg::read) this register and get [`iram0_exception_monitor_0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@iram0_exception_monitor_0`] module"]
pub type IRAM0_EXCEPTION_MONITOR_0 =
    crate::Reg<iram0_exception_monitor_0::IRAM0_EXCEPTION_MONITOR_0_SPEC>;
#[doc = "exception monitor status register0"]
pub mod iram0_exception_monitor_0;
#[doc = "IRAM0_EXCEPTION_MONITOR_1 (r) register accessor: exception monitor status register1\n\nYou can [`read`](crate::Reg::read) this register and get [`iram0_exception_monitor_1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@iram0_exception_monitor_1`] module"]
pub type IRAM0_EXCEPTION_MONITOR_1 =
    crate::Reg<iram0_exception_monitor_1::IRAM0_EXCEPTION_MONITOR_1_SPEC>;
#[doc = "exception monitor status register1"]
pub mod iram0_exception_monitor_1;
#[doc = "LASTPC_BEFORE_EXCEPTION (r) register accessor: ASSIST_DEBUG_CORE_0_LASTPC_BEFORE_EXCEPTION\n\nYou can [`read`](crate::Reg::read) this register and get [`lastpc_before_exception::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lastpc_before_exception`] module"]
pub type LASTPC_BEFORE_EXCEPTION =
    crate::Reg<lastpc_before_exception::LASTPC_BEFORE_EXCEPTION_SPEC>;
#[doc = "ASSIST_DEBUG_CORE_0_LASTPC_BEFORE_EXCEPTION"]
pub mod lastpc_before_exception;
#[doc = "MONTR_ENA (rw) register accessor: ASSIST_DEBUG_CORE_0_MONTR_ENA_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`montr_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`montr_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@montr_ena`] module"]
pub type MONTR_ENA = crate::Reg<montr_ena::MONTR_ENA_SPEC>;
#[doc = "ASSIST_DEBUG_CORE_0_MONTR_ENA_REG"]
pub mod montr_ena;
#[doc = "RCD_EN (rw) register accessor: record enable configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`rcd_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rcd_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rcd_en`] module"]
pub type RCD_EN = crate::Reg<rcd_en::RCD_EN_SPEC>;
#[doc = "record enable configuration register"]
pub mod rcd_en;
#[doc = "RCD_PDEBUGPC (r) register accessor: record status regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`rcd_pdebugpc::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rcd_pdebugpc`] module"]
pub type RCD_PDEBUGPC = crate::Reg<rcd_pdebugpc::RCD_PDEBUGPC_SPEC>;
#[doc = "record status regsiter"]
pub mod rcd_pdebugpc;
#[doc = "RCD_PDEBUGSP (r) register accessor: record status regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`rcd_pdebugsp::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rcd_pdebugsp`] module"]
pub type RCD_PDEBUGSP = crate::Reg<rcd_pdebugsp::RCD_PDEBUGSP_SPEC>;
#[doc = "record status regsiter"]
pub mod rcd_pdebugsp;
#[doc = "SP_MAX (rw) register accessor: stack max value\n\nYou can [`read`](crate::Reg::read) this register and get [`sp_max::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sp_max::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sp_max`] module"]
pub type SP_MAX = crate::Reg<sp_max::SP_MAX_SPEC>;
#[doc = "stack max value"]
pub mod sp_max;
#[doc = "SP_MIN (rw) register accessor: stack min value\n\nYou can [`read`](crate::Reg::read) this register and get [`sp_min::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sp_min::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sp_min`] module"]
pub type SP_MIN = crate::Reg<sp_min::SP_MIN_SPEC>;
#[doc = "stack min value"]
pub mod sp_min;
#[doc = "SP_PC (r) register accessor: stack monitor pc status register\n\nYou can [`read`](crate::Reg::read) this register and get [`sp_pc::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sp_pc`] module"]
pub type SP_PC = crate::Reg<sp_pc::SP_PC_SPEC>;
#[doc = "stack monitor pc status register"]
pub mod sp_pc;
