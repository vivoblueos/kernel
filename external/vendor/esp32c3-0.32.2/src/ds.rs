#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    y_mem: [Y_MEM; 128],
    m_mem: [M_MEM; 128],
    rb_mem: [RB_MEM; 128],
    box_mem: [BOX_MEM; 12],
    iv_mem: [IV_MEM; 4],
    _reserved5: [u8; 0x01c0],
    x_mem: [X_MEM; 128],
    z_mem: [Z_MEM; 128],
    _reserved7: [u8; 0x0200],
    set_start: SET_START,
    set_continue: SET_CONTINUE,
    set_finish: SET_FINISH,
    query_busy: QUERY_BUSY,
    query_key_wrong: QUERY_KEY_WRONG,
    query_check: QUERY_CHECK,
    _reserved13: [u8; 0x08],
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00..0x200 - memory that stores Y"]
    #[inline(always)]
    pub const fn y_mem(&self, n: usize) -> &Y_MEM {
        &self.y_mem[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x00..0x200 - memory that stores Y"]
    #[inline(always)]
    pub fn y_mem_iter(&self) -> impl Iterator<Item = &Y_MEM> {
        self.y_mem.iter()
    }
    #[doc = "0x200..0x400 - memory that stores M"]
    #[inline(always)]
    pub const fn m_mem(&self, n: usize) -> &M_MEM {
        &self.m_mem[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x200..0x400 - memory that stores M"]
    #[inline(always)]
    pub fn m_mem_iter(&self) -> impl Iterator<Item = &M_MEM> {
        self.m_mem.iter()
    }
    #[doc = "0x400..0x600 - memory that stores Rb"]
    #[inline(always)]
    pub const fn rb_mem(&self, n: usize) -> &RB_MEM {
        &self.rb_mem[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x400..0x600 - memory that stores Rb"]
    #[inline(always)]
    pub fn rb_mem_iter(&self) -> impl Iterator<Item = &RB_MEM> {
        self.rb_mem.iter()
    }
    #[doc = "0x600..0x630 - memory that stores BOX"]
    #[inline(always)]
    pub const fn box_mem(&self, n: usize) -> &BOX_MEM {
        &self.box_mem[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x600..0x630 - memory that stores BOX"]
    #[inline(always)]
    pub fn box_mem_iter(&self) -> impl Iterator<Item = &BOX_MEM> {
        self.box_mem.iter()
    }
    #[doc = "0x630..0x640 - IV block data"]
    #[inline(always)]
    pub const fn iv_mem(&self, n: usize) -> &IV_MEM {
        &self.iv_mem[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x630..0x640 - IV block data"]
    #[inline(always)]
    pub fn iv_mem_iter(&self) -> impl Iterator<Item = &IV_MEM> {
        self.iv_mem.iter()
    }
    #[doc = "0x800..0xa00 - memory that stores X"]
    #[inline(always)]
    pub const fn x_mem(&self, n: usize) -> &X_MEM {
        &self.x_mem[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x800..0xa00 - memory that stores X"]
    #[inline(always)]
    pub fn x_mem_iter(&self) -> impl Iterator<Item = &X_MEM> {
        self.x_mem.iter()
    }
    #[doc = "0xa00..0xc00 - memory that stores Z"]
    #[inline(always)]
    pub const fn z_mem(&self, n: usize) -> &Z_MEM {
        &self.z_mem[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0xa00..0xc00 - memory that stores Z"]
    #[inline(always)]
    pub fn z_mem_iter(&self) -> impl Iterator<Item = &Z_MEM> {
        self.z_mem.iter()
    }
    #[doc = "0xe00 - DS start control register"]
    #[inline(always)]
    pub const fn set_start(&self) -> &SET_START {
        &self.set_start
    }
    #[doc = "0xe04 - DS continue control register"]
    #[inline(always)]
    pub const fn set_continue(&self) -> &SET_CONTINUE {
        &self.set_continue
    }
    #[doc = "0xe08 - DS finish control register"]
    #[inline(always)]
    pub const fn set_finish(&self) -> &SET_FINISH {
        &self.set_finish
    }
    #[doc = "0xe0c - DS query busy register"]
    #[inline(always)]
    pub const fn query_busy(&self) -> &QUERY_BUSY {
        &self.query_busy
    }
    #[doc = "0xe10 - DS query key-wrong counter register"]
    #[inline(always)]
    pub const fn query_key_wrong(&self) -> &QUERY_KEY_WRONG {
        &self.query_key_wrong
    }
    #[doc = "0xe14 - DS query check result register"]
    #[inline(always)]
    pub const fn query_check(&self) -> &QUERY_CHECK {
        &self.query_check
    }
    #[doc = "0xe20 - DS version control register"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "Y_MEM (rw) register accessor: memory that stores Y\n\nYou can [`read`](crate::Reg::read) this register and get [`y_mem::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`y_mem::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@y_mem`] module"]
pub type Y_MEM = crate::Reg<y_mem::Y_MEM_SPEC>;
#[doc = "memory that stores Y"]
pub mod y_mem;
#[doc = "M_MEM (rw) register accessor: memory that stores M\n\nYou can [`read`](crate::Reg::read) this register and get [`m_mem::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`m_mem::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@m_mem`] module"]
pub type M_MEM = crate::Reg<m_mem::M_MEM_SPEC>;
#[doc = "memory that stores M"]
pub mod m_mem;
#[doc = "RB_MEM (rw) register accessor: memory that stores Rb\n\nYou can [`read`](crate::Reg::read) this register and get [`rb_mem::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rb_mem::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rb_mem`] module"]
pub type RB_MEM = crate::Reg<rb_mem::RB_MEM_SPEC>;
#[doc = "memory that stores Rb"]
pub mod rb_mem;
#[doc = "BOX_MEM (rw) register accessor: memory that stores BOX\n\nYou can [`read`](crate::Reg::read) this register and get [`box_mem::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`box_mem::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@box_mem`] module"]
pub type BOX_MEM = crate::Reg<box_mem::BOX_MEM_SPEC>;
#[doc = "memory that stores BOX"]
pub mod box_mem;
#[doc = "IV_MEM (rw) register accessor: IV block data\n\nYou can [`read`](crate::Reg::read) this register and get [`iv_mem::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`iv_mem::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@iv_mem`] module"]
pub type IV_MEM = crate::Reg<iv_mem::IV_MEM_SPEC>;
#[doc = "IV block data"]
pub mod iv_mem;
#[doc = "X_MEM (rw) register accessor: memory that stores X\n\nYou can [`read`](crate::Reg::read) this register and get [`x_mem::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`x_mem::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@x_mem`] module"]
pub type X_MEM = crate::Reg<x_mem::X_MEM_SPEC>;
#[doc = "memory that stores X"]
pub mod x_mem;
#[doc = "Z_MEM (rw) register accessor: memory that stores Z\n\nYou can [`read`](crate::Reg::read) this register and get [`z_mem::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`z_mem::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@z_mem`] module"]
pub type Z_MEM = crate::Reg<z_mem::Z_MEM_SPEC>;
#[doc = "memory that stores Z"]
pub mod z_mem;
#[doc = "SET_START (w) register accessor: DS start control register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`set_start::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@set_start`] module"]
pub type SET_START = crate::Reg<set_start::SET_START_SPEC>;
#[doc = "DS start control register"]
pub mod set_start;
#[doc = "SET_CONTINUE (w) register accessor: DS continue control register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`set_continue::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@set_continue`] module"]
pub type SET_CONTINUE = crate::Reg<set_continue::SET_CONTINUE_SPEC>;
#[doc = "DS continue control register"]
pub mod set_continue;
#[doc = "SET_FINISH (w) register accessor: DS finish control register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`set_finish::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@set_finish`] module"]
pub type SET_FINISH = crate::Reg<set_finish::SET_FINISH_SPEC>;
#[doc = "DS finish control register"]
pub mod set_finish;
#[doc = "QUERY_BUSY (r) register accessor: DS query busy register\n\nYou can [`read`](crate::Reg::read) this register and get [`query_busy::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@query_busy`] module"]
pub type QUERY_BUSY = crate::Reg<query_busy::QUERY_BUSY_SPEC>;
#[doc = "DS query busy register"]
pub mod query_busy;
#[doc = "QUERY_KEY_WRONG (r) register accessor: DS query key-wrong counter register\n\nYou can [`read`](crate::Reg::read) this register and get [`query_key_wrong::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@query_key_wrong`] module"]
pub type QUERY_KEY_WRONG = crate::Reg<query_key_wrong::QUERY_KEY_WRONG_SPEC>;
#[doc = "DS query key-wrong counter register"]
pub mod query_key_wrong;
#[doc = "QUERY_CHECK (r) register accessor: DS query check result register\n\nYou can [`read`](crate::Reg::read) this register and get [`query_check::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@query_check`] module"]
pub type QUERY_CHECK = crate::Reg<query_check::QUERY_CHECK_SPEC>;
#[doc = "DS query check result register"]
pub mod query_check;
pub use crate::aes::{date, DATE};
