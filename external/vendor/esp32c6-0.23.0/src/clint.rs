#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    _reserved0: [u8; 0x1800],
    msip: MSIP,
    mtimectl: MTIMECTL,
    mtime: MTIME,
    mtimecmp: MTIMECMP,
    _reserved4: [u8; 0x03e8],
    usip: USIP,
    utimectl: UTIMECTL,
    utime: UTIME,
    utimecmp: UTIMECMP,
}
impl RegisterBlock {
    #[doc = "0x1800 - "]
    #[inline(always)]
    pub const fn msip(&self) -> &MSIP {
        &self.msip
    }
    #[doc = "0x1804 - "]
    #[inline(always)]
    pub const fn mtimectl(&self) -> &MTIMECTL {
        &self.mtimectl
    }
    #[doc = "0x1808..0x1810 - "]
    #[inline(always)]
    pub const fn mtime(&self) -> &MTIME {
        &self.mtime
    }
    #[doc = "0x1810..0x1818 - "]
    #[inline(always)]
    pub const fn mtimecmp(&self) -> &MTIMECMP {
        &self.mtimecmp
    }
    #[doc = "0x1c00 - "]
    #[inline(always)]
    pub const fn usip(&self) -> &USIP {
        &self.usip
    }
    #[doc = "0x1c04 - "]
    #[inline(always)]
    pub const fn utimectl(&self) -> &UTIMECTL {
        &self.utimectl
    }
    #[doc = "0x1c08..0x1c10 - "]
    #[inline(always)]
    pub const fn utime(&self) -> &UTIME {
        &self.utime
    }
    #[doc = "0x1c10..0x1c18 - "]
    #[inline(always)]
    pub const fn utimecmp(&self) -> &UTIMECMP {
        &self.utimecmp
    }
}
#[doc = "MSIP (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`msip::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`msip::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@msip`] module"]
pub type MSIP = crate::Reg<msip::MSIP_SPEC>;
#[doc = ""]
pub mod msip;
#[doc = "MTIMECTL (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`mtimectl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mtimectl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtimectl`] module"]
pub type MTIMECTL = crate::Reg<mtimectl::MTIMECTL_SPEC>;
#[doc = ""]
pub mod mtimectl;
#[doc = "MTIME (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`mtime::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mtime::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtime`] module"]
pub type MTIME = crate::Reg<mtime::MTIME_SPEC>;
#[doc = ""]
pub mod mtime;
#[doc = "MTIMECMP (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`mtimecmp::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mtimecmp::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtimecmp`] module"]
pub type MTIMECMP = crate::Reg<mtimecmp::MTIMECMP_SPEC>;
#[doc = ""]
pub mod mtimecmp;
#[doc = "USIP (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`usip::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`usip::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@usip`] module"]
pub type USIP = crate::Reg<usip::USIP_SPEC>;
#[doc = ""]
pub mod usip;
#[doc = "UTIMECTL (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`utimectl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`utimectl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@utimectl`] module"]
pub type UTIMECTL = crate::Reg<utimectl::UTIMECTL_SPEC>;
#[doc = ""]
pub mod utimectl;
#[doc = "UTIME (r) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`utime::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@utime`] module"]
pub type UTIME = crate::Reg<utime::UTIME_SPEC>;
#[doc = ""]
pub mod utime;
#[doc = "UTIMECMP (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`utimecmp::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`utimecmp::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@utimecmp`] module"]
pub type UTIMECMP = crate::Reg<utimecmp::UTIMECMP_SPEC>;
#[doc = ""]
pub mod utimecmp;
