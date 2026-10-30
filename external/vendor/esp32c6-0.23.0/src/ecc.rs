#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    _reserved0: [u8; 0x0c],
    mult_int_raw: MULT_INT_RAW,
    mult_int_st: MULT_INT_ST,
    mult_int_ena: MULT_INT_ENA,
    mult_int_clr: MULT_INT_CLR,
    mult_conf: MULT_CONF,
    _reserved5: [u8; 0xdc],
    mult_date: MULT_DATE,
    k_mem: [K_MEM; 8],
    px_mem: [PX_MEM; 8],
    py_mem: [PY_MEM; 8],
}
impl RegisterBlock {
    #[doc = "0x0c - ECC interrupt raw register, valid in level."]
    #[inline(always)]
    pub const fn mult_int_raw(&self) -> &MULT_INT_RAW {
        &self.mult_int_raw
    }
    #[doc = "0x10 - ECC interrupt status register."]
    #[inline(always)]
    pub const fn mult_int_st(&self) -> &MULT_INT_ST {
        &self.mult_int_st
    }
    #[doc = "0x14 - ECC interrupt enable register."]
    #[inline(always)]
    pub const fn mult_int_ena(&self) -> &MULT_INT_ENA {
        &self.mult_int_ena
    }
    #[doc = "0x18 - ECC interrupt clear register."]
    #[inline(always)]
    pub const fn mult_int_clr(&self) -> &MULT_INT_CLR {
        &self.mult_int_clr
    }
    #[doc = "0x1c - ECC configure register"]
    #[inline(always)]
    pub const fn mult_conf(&self) -> &MULT_CONF {
        &self.mult_conf
    }
    #[doc = "0xfc - Version control register"]
    #[inline(always)]
    pub const fn mult_date(&self) -> &MULT_DATE {
        &self.mult_date
    }
    #[doc = "0x100..0x120 - The memory that stores k."]
    #[inline(always)]
    pub const fn k_mem(&self, n: usize) -> &K_MEM {
        &self.k_mem[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x100..0x120 - The memory that stores k."]
    #[inline(always)]
    pub fn k_mem_iter(&self) -> impl Iterator<Item = &K_MEM> {
        self.k_mem.iter()
    }
    #[doc = "0x120..0x140 - The memory that stores Px."]
    #[inline(always)]
    pub const fn px_mem(&self, n: usize) -> &PX_MEM {
        &self.px_mem[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x120..0x140 - The memory that stores Px."]
    #[inline(always)]
    pub fn px_mem_iter(&self) -> impl Iterator<Item = &PX_MEM> {
        self.px_mem.iter()
    }
    #[doc = "0x140..0x160 - The memory that stores Py."]
    #[inline(always)]
    pub const fn py_mem(&self, n: usize) -> &PY_MEM {
        &self.py_mem[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x140..0x160 - The memory that stores Py."]
    #[inline(always)]
    pub fn py_mem_iter(&self) -> impl Iterator<Item = &PY_MEM> {
        self.py_mem.iter()
    }
}
#[doc = "MULT_INT_RAW (r) register accessor: ECC interrupt raw register, valid in level.\n\nYou can [`read`](crate::Reg::read) this register and get [`mult_int_raw::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mult_int_raw`] module"]
pub type MULT_INT_RAW = crate::Reg<mult_int_raw::MULT_INT_RAW_SPEC>;
#[doc = "ECC interrupt raw register, valid in level."]
pub mod mult_int_raw;
#[doc = "MULT_INT_ST (r) register accessor: ECC interrupt status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`mult_int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mult_int_st`] module"]
pub type MULT_INT_ST = crate::Reg<mult_int_st::MULT_INT_ST_SPEC>;
#[doc = "ECC interrupt status register."]
pub mod mult_int_st;
#[doc = "MULT_INT_ENA (rw) register accessor: ECC interrupt enable register.\n\nYou can [`read`](crate::Reg::read) this register and get [`mult_int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mult_int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mult_int_ena`] module"]
pub type MULT_INT_ENA = crate::Reg<mult_int_ena::MULT_INT_ENA_SPEC>;
#[doc = "ECC interrupt enable register."]
pub mod mult_int_ena;
#[doc = "MULT_INT_CLR (w) register accessor: ECC interrupt clear register.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mult_int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mult_int_clr`] module"]
pub type MULT_INT_CLR = crate::Reg<mult_int_clr::MULT_INT_CLR_SPEC>;
#[doc = "ECC interrupt clear register."]
pub mod mult_int_clr;
#[doc = "MULT_CONF (rw) register accessor: ECC configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`mult_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mult_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mult_conf`] module"]
pub type MULT_CONF = crate::Reg<mult_conf::MULT_CONF_SPEC>;
#[doc = "ECC configure register"]
pub mod mult_conf;
pub use crate::aes::{date as mult_date, DATE as MULT_DATE};
#[doc = "K_MEM (rw) register accessor: The memory that stores k.\n\nYou can [`read`](crate::Reg::read) this register and get [`k_mem::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`k_mem::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@k_mem`] module"]
pub type K_MEM = crate::Reg<k_mem::K_MEM_SPEC>;
#[doc = "The memory that stores k."]
pub mod k_mem;
#[doc = "PX_MEM (rw) register accessor: The memory that stores Px.\n\nYou can [`read`](crate::Reg::read) this register and get [`px_mem::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`px_mem::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@px_mem`] module"]
pub type PX_MEM = crate::Reg<px_mem::PX_MEM_SPEC>;
#[doc = "The memory that stores Px."]
pub mod px_mem;
#[doc = "PY_MEM (rw) register accessor: The memory that stores Py.\n\nYou can [`read`](crate::Reg::read) this register and get [`py_mem::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`py_mem::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@py_mem`] module"]
pub type PY_MEM = crate::Reg<py_mem::PY_MEM_SPEC>;
#[doc = "The memory that stores Py."]
pub mod py_mem;
