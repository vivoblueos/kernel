#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    mxint_enable: MXINT_ENABLE,
    mxint_type: MXINT_TYPE,
    mxint_clear: MXINT_CLEAR,
    emip_status: EMIP_STATUS,
    mxint_pri: [MXINT_PRI; 32],
    mxint_thresh: MXINT_THRESH,
    mxint_claim: MXINT_CLAIM,
}
impl RegisterBlock {
    #[doc = "0x00 - PLIC MX Interrupt Enable Register"]
    #[inline(always)]
    pub const fn mxint_enable(&self) -> &MXINT_ENABLE {
        &self.mxint_enable
    }
    #[doc = "0x04 - PLIC MX Interrupt Type Register"]
    #[inline(always)]
    pub const fn mxint_type(&self) -> &MXINT_TYPE {
        &self.mxint_type
    }
    #[doc = "0x08 - PLIC MX Interrupt Clear Register"]
    #[inline(always)]
    pub const fn mxint_clear(&self) -> &MXINT_CLEAR {
        &self.mxint_clear
    }
    #[doc = "0x0c - PLIC EMIP Status Register"]
    #[inline(always)]
    pub const fn emip_status(&self) -> &EMIP_STATUS {
        &self.emip_status
    }
    #[doc = "0x10..0x90 - PLIC MX Interrupt %s Priority Register"]
    #[inline(always)]
    pub const fn mxint_pri(&self, n: usize) -> &MXINT_PRI {
        &self.mxint_pri[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x10..0x90 - PLIC MX Interrupt %s Priority Register"]
    #[inline(always)]
    pub fn mxint_pri_iter(&self) -> impl Iterator<Item = &MXINT_PRI> {
        self.mxint_pri.iter()
    }
    #[doc = "0x10 - PLIC MX Interrupt 0 Priority Register"]
    #[inline(always)]
    pub const fn mxint0_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(0)
    }
    #[doc = "0x14 - PLIC MX Interrupt 1 Priority Register"]
    #[inline(always)]
    pub const fn mxint1_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(1)
    }
    #[doc = "0x18 - PLIC MX Interrupt 2 Priority Register"]
    #[inline(always)]
    pub const fn mxint2_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(2)
    }
    #[doc = "0x1c - PLIC MX Interrupt 3 Priority Register"]
    #[inline(always)]
    pub const fn mxint3_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(3)
    }
    #[doc = "0x20 - PLIC MX Interrupt 4 Priority Register"]
    #[inline(always)]
    pub const fn mxint4_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(4)
    }
    #[doc = "0x24 - PLIC MX Interrupt 5 Priority Register"]
    #[inline(always)]
    pub const fn mxint5_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(5)
    }
    #[doc = "0x28 - PLIC MX Interrupt 6 Priority Register"]
    #[inline(always)]
    pub const fn mxint6_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(6)
    }
    #[doc = "0x2c - PLIC MX Interrupt 7 Priority Register"]
    #[inline(always)]
    pub const fn mxint7_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(7)
    }
    #[doc = "0x30 - PLIC MX Interrupt 8 Priority Register"]
    #[inline(always)]
    pub const fn mxint8_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(8)
    }
    #[doc = "0x34 - PLIC MX Interrupt 9 Priority Register"]
    #[inline(always)]
    pub const fn mxint9_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(9)
    }
    #[doc = "0x38 - PLIC MX Interrupt 10 Priority Register"]
    #[inline(always)]
    pub const fn mxint10_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(10)
    }
    #[doc = "0x3c - PLIC MX Interrupt 11 Priority Register"]
    #[inline(always)]
    pub const fn mxint11_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(11)
    }
    #[doc = "0x40 - PLIC MX Interrupt 12 Priority Register"]
    #[inline(always)]
    pub const fn mxint12_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(12)
    }
    #[doc = "0x44 - PLIC MX Interrupt 13 Priority Register"]
    #[inline(always)]
    pub const fn mxint13_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(13)
    }
    #[doc = "0x48 - PLIC MX Interrupt 14 Priority Register"]
    #[inline(always)]
    pub const fn mxint14_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(14)
    }
    #[doc = "0x4c - PLIC MX Interrupt 15 Priority Register"]
    #[inline(always)]
    pub const fn mxint15_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(15)
    }
    #[doc = "0x50 - PLIC MX Interrupt 16 Priority Register"]
    #[inline(always)]
    pub const fn mxint16_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(16)
    }
    #[doc = "0x54 - PLIC MX Interrupt 17 Priority Register"]
    #[inline(always)]
    pub const fn mxint17_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(17)
    }
    #[doc = "0x58 - PLIC MX Interrupt 18 Priority Register"]
    #[inline(always)]
    pub const fn mxint18_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(18)
    }
    #[doc = "0x5c - PLIC MX Interrupt 19 Priority Register"]
    #[inline(always)]
    pub const fn mxint19_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(19)
    }
    #[doc = "0x60 - PLIC MX Interrupt 20 Priority Register"]
    #[inline(always)]
    pub const fn mxint20_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(20)
    }
    #[doc = "0x64 - PLIC MX Interrupt 21 Priority Register"]
    #[inline(always)]
    pub const fn mxint21_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(21)
    }
    #[doc = "0x68 - PLIC MX Interrupt 22 Priority Register"]
    #[inline(always)]
    pub const fn mxint22_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(22)
    }
    #[doc = "0x6c - PLIC MX Interrupt 23 Priority Register"]
    #[inline(always)]
    pub const fn mxint23_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(23)
    }
    #[doc = "0x70 - PLIC MX Interrupt 24 Priority Register"]
    #[inline(always)]
    pub const fn mxint24_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(24)
    }
    #[doc = "0x74 - PLIC MX Interrupt 25 Priority Register"]
    #[inline(always)]
    pub const fn mxint25_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(25)
    }
    #[doc = "0x78 - PLIC MX Interrupt 26 Priority Register"]
    #[inline(always)]
    pub const fn mxint26_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(26)
    }
    #[doc = "0x7c - PLIC MX Interrupt 27 Priority Register"]
    #[inline(always)]
    pub const fn mxint27_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(27)
    }
    #[doc = "0x80 - PLIC MX Interrupt 28 Priority Register"]
    #[inline(always)]
    pub const fn mxint28_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(28)
    }
    #[doc = "0x84 - PLIC MX Interrupt 29 Priority Register"]
    #[inline(always)]
    pub const fn mxint29_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(29)
    }
    #[doc = "0x88 - PLIC MX Interrupt 30 Priority Register"]
    #[inline(always)]
    pub const fn mxint30_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(30)
    }
    #[doc = "0x8c - PLIC MX Interrupt 31 Priority Register"]
    #[inline(always)]
    pub const fn mxint31_pri(&self) -> &MXINT_PRI {
        self.mxint_pri(31)
    }
    #[doc = "0x90 - PLIC MX Interrupt Threshold Register"]
    #[inline(always)]
    pub const fn mxint_thresh(&self) -> &MXINT_THRESH {
        &self.mxint_thresh
    }
    #[doc = "0x94 - PLIC MX Interrupt Claim Register"]
    #[inline(always)]
    pub const fn mxint_claim(&self) -> &MXINT_CLAIM {
        &self.mxint_claim
    }
}
#[doc = "MXINT_ENABLE (rw) register accessor: PLIC MX Interrupt Enable Register\n\nYou can [`read`](crate::Reg::read) this register and get [`mxint_enable::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mxint_enable::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mxint_enable`] module"]
pub type MXINT_ENABLE = crate::Reg<mxint_enable::MXINT_ENABLE_SPEC>;
#[doc = "PLIC MX Interrupt Enable Register"]
pub mod mxint_enable;
#[doc = "MXINT_TYPE (rw) register accessor: PLIC MX Interrupt Type Register\n\nYou can [`read`](crate::Reg::read) this register and get [`mxint_type::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mxint_type::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mxint_type`] module"]
pub type MXINT_TYPE = crate::Reg<mxint_type::MXINT_TYPE_SPEC>;
#[doc = "PLIC MX Interrupt Type Register"]
pub mod mxint_type;
#[doc = "MXINT_CLEAR (rw) register accessor: PLIC MX Interrupt Clear Register\n\nYou can [`read`](crate::Reg::read) this register and get [`mxint_clear::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mxint_clear::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mxint_clear`] module"]
pub type MXINT_CLEAR = crate::Reg<mxint_clear::MXINT_CLEAR_SPEC>;
#[doc = "PLIC MX Interrupt Clear Register"]
pub mod mxint_clear;
#[doc = "EMIP_STATUS (r) register accessor: PLIC EMIP Status Register\n\nYou can [`read`](crate::Reg::read) this register and get [`emip_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@emip_status`] module"]
pub type EMIP_STATUS = crate::Reg<emip_status::EMIP_STATUS_SPEC>;
#[doc = "PLIC EMIP Status Register"]
pub mod emip_status;
#[doc = "MXINT_PRI (rw) register accessor: PLIC MX Interrupt %s Priority Register\n\nYou can [`read`](crate::Reg::read) this register and get [`mxint_pri::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mxint_pri::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mxint_pri`] module"]
pub type MXINT_PRI = crate::Reg<mxint_pri::MXINT_PRI_SPEC>;
#[doc = "PLIC MX Interrupt %s Priority Register"]
pub mod mxint_pri;
#[doc = "MXINT_THRESH (rw) register accessor: PLIC MX Interrupt Threshold Register\n\nYou can [`read`](crate::Reg::read) this register and get [`mxint_thresh::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mxint_thresh::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mxint_thresh`] module"]
pub type MXINT_THRESH = crate::Reg<mxint_thresh::MXINT_THRESH_SPEC>;
#[doc = "PLIC MX Interrupt Threshold Register"]
pub mod mxint_thresh;
#[doc = "MXINT_CLAIM (rw) register accessor: PLIC MX Interrupt Claim Register\n\nYou can [`read`](crate::Reg::read) this register and get [`mxint_claim::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mxint_claim::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mxint_claim`] module"]
pub type MXINT_CLAIM = crate::Reg<mxint_claim::MXINT_CLAIM_SPEC>;
#[doc = "PLIC MX Interrupt Claim Register"]
pub mod mxint_claim;
