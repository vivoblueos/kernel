#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster T%s, containing T?CONFIG, T?LO, T?HI, T?UPDATE, T?ALARMLO, T?ALARMHI, T?LOADLO, T?LOADHI, T?LOAD"]
pub struct T {
    config: CONFIG,
    lo: LO,
    hi: HI,
    update: UPDATE,
    alarmlo: ALARMLO,
    alarmhi: ALARMHI,
    loadlo: LOADLO,
    loadhi: LOADHI,
    load: LOAD,
}
impl T {
    #[doc = "0x00 - Timer %s configuration register"]
    #[inline(always)]
    pub const fn config(&self) -> &CONFIG {
        &self.config
    }
    #[doc = "0x04 - Timer %s current value, low 32 bits"]
    #[inline(always)]
    pub const fn lo(&self) -> &LO {
        &self.lo
    }
    #[doc = "0x08 - Timer %s current value, high 22 bits"]
    #[inline(always)]
    pub const fn hi(&self) -> &HI {
        &self.hi
    }
    #[doc = "0x0c - Write to copy current timer value to TIMGn_T%s_(LO/HI)_REG"]
    #[inline(always)]
    pub const fn update(&self) -> &UPDATE {
        &self.update
    }
    #[doc = "0x10 - Timer %s alarm value, low 32 bits"]
    #[inline(always)]
    pub const fn alarmlo(&self) -> &ALARMLO {
        &self.alarmlo
    }
    #[doc = "0x14 - Timer %s alarm value, high bits"]
    #[inline(always)]
    pub const fn alarmhi(&self) -> &ALARMHI {
        &self.alarmhi
    }
    #[doc = "0x18 - Timer %s reload value, low 32 bits"]
    #[inline(always)]
    pub const fn loadlo(&self) -> &LOADLO {
        &self.loadlo
    }
    #[doc = "0x1c - Timer %s reload value, high 22 bits"]
    #[inline(always)]
    pub const fn loadhi(&self) -> &LOADHI {
        &self.loadhi
    }
    #[doc = "0x20 - Write to reload timer from TIMG_T%s_(LOADLOLOADHI)_REG"]
    #[inline(always)]
    pub const fn load(&self) -> &LOAD {
        &self.load
    }
}
#[doc = "CONFIG (rw) register accessor: Timer %s configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`config::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`config::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@config`] module"]
pub type CONFIG = crate::Reg<config::CONFIG_SPEC>;
#[doc = "Timer %s configuration register"]
pub mod config;
#[doc = "LO (r) register accessor: Timer %s current value, low 32 bits\n\nYou can [`read`](crate::Reg::read) this register and get [`lo::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lo`] module"]
pub type LO = crate::Reg<lo::LO_SPEC>;
#[doc = "Timer %s current value, low 32 bits"]
pub mod lo;
#[doc = "HI (r) register accessor: Timer %s current value, high 22 bits\n\nYou can [`read`](crate::Reg::read) this register and get [`hi::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hi`] module"]
pub type HI = crate::Reg<hi::HI_SPEC>;
#[doc = "Timer %s current value, high 22 bits"]
pub mod hi;
#[doc = "UPDATE (rw) register accessor: Write to copy current timer value to TIMGn_T%s_(LO/HI)_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`update::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`update::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@update`] module"]
pub type UPDATE = crate::Reg<update::UPDATE_SPEC>;
#[doc = "Write to copy current timer value to TIMGn_T%s_(LO/HI)_REG"]
pub mod update;
#[doc = "ALARMLO (rw) register accessor: Timer %s alarm value, low 32 bits\n\nYou can [`read`](crate::Reg::read) this register and get [`alarmlo::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`alarmlo::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@alarmlo`] module"]
pub type ALARMLO = crate::Reg<alarmlo::ALARMLO_SPEC>;
#[doc = "Timer %s alarm value, low 32 bits"]
pub mod alarmlo;
#[doc = "ALARMHI (rw) register accessor: Timer %s alarm value, high bits\n\nYou can [`read`](crate::Reg::read) this register and get [`alarmhi::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`alarmhi::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@alarmhi`] module"]
pub type ALARMHI = crate::Reg<alarmhi::ALARMHI_SPEC>;
#[doc = "Timer %s alarm value, high bits"]
pub mod alarmhi;
#[doc = "LOADLO (rw) register accessor: Timer %s reload value, low 32 bits\n\nYou can [`read`](crate::Reg::read) this register and get [`loadlo::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`loadlo::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@loadlo`] module"]
pub type LOADLO = crate::Reg<loadlo::LOADLO_SPEC>;
#[doc = "Timer %s reload value, low 32 bits"]
pub mod loadlo;
#[doc = "LOADHI (rw) register accessor: Timer %s reload value, high 22 bits\n\nYou can [`read`](crate::Reg::read) this register and get [`loadhi::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`loadhi::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@loadhi`] module"]
pub type LOADHI = crate::Reg<loadhi::LOADHI_SPEC>;
#[doc = "Timer %s reload value, high 22 bits"]
pub mod loadhi;
#[doc = "LOAD (w) register accessor: Write to reload timer from TIMG_T%s_(LOADLOLOADHI)_REG\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`load::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@load`] module"]
pub type LOAD = crate::Reg<load::LOAD_SPEC>;
#[doc = "Write to reload timer from TIMG_T%s_(LOADLOLOADHI)_REG"]
pub mod load;
