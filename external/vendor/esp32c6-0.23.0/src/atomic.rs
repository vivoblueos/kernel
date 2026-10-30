#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    addr_lock: ADDR_LOCK,
    lr_addr: LR_ADDR,
    lr_value: LR_VALUE,
    lock_status: LOCK_STATUS,
    counter: COUNTER,
}
impl RegisterBlock {
    #[doc = "0x00 - hardware lock regsiter"]
    #[inline(always)]
    pub const fn addr_lock(&self) -> &ADDR_LOCK {
        &self.addr_lock
    }
    #[doc = "0x04 - gloable lr address regsiter"]
    #[inline(always)]
    pub const fn lr_addr(&self) -> &LR_ADDR {
        &self.lr_addr
    }
    #[doc = "0x08 - gloable lr value regsiter"]
    #[inline(always)]
    pub const fn lr_value(&self) -> &LR_VALUE {
        &self.lr_value
    }
    #[doc = "0x0c - lock status regsiter"]
    #[inline(always)]
    pub const fn lock_status(&self) -> &LOCK_STATUS {
        &self.lock_status
    }
    #[doc = "0x10 - wait counter register"]
    #[inline(always)]
    pub const fn counter(&self) -> &COUNTER {
        &self.counter
    }
}
#[doc = "ADDR_LOCK (rw) register accessor: hardware lock regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`addr_lock::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`addr_lock::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@addr_lock`] module"]
pub type ADDR_LOCK = crate::Reg<addr_lock::ADDR_LOCK_SPEC>;
#[doc = "hardware lock regsiter"]
pub mod addr_lock;
#[doc = "LR_ADDR (rw) register accessor: gloable lr address regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`lr_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lr_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lr_addr`] module"]
pub type LR_ADDR = crate::Reg<lr_addr::LR_ADDR_SPEC>;
#[doc = "gloable lr address regsiter"]
pub mod lr_addr;
#[doc = "LR_VALUE (rw) register accessor: gloable lr value regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`lr_value::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lr_value::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lr_value`] module"]
pub type LR_VALUE = crate::Reg<lr_value::LR_VALUE_SPEC>;
#[doc = "gloable lr value regsiter"]
pub mod lr_value;
#[doc = "LOCK_STATUS (r) register accessor: lock status regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`lock_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lock_status`] module"]
pub type LOCK_STATUS = crate::Reg<lock_status::LOCK_STATUS_SPEC>;
#[doc = "lock status regsiter"]
pub mod lock_status;
#[doc = "COUNTER (rw) register accessor: wait counter register\n\nYou can [`read`](crate::Reg::read) this register and get [`counter::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`counter::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@counter`] module"]
pub type COUNTER = crate::Reg<counter::COUNTER_SPEC>;
#[doc = "wait counter register"]
pub mod counter;
