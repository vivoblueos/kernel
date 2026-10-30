#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    uxint_enable: UXINT_ENABLE,
    uxint_type: UXINT_TYPE,
    uxint_clear: UXINT_CLEAR,
    euip_status: EUIP_STATUS,
    uxint_pri: [UXINT_PRI; 32],
    uxint_thresh: UXINT_THRESH,
    uxint_claim: UXINT_CLAIM,
}
impl RegisterBlock {
    #[doc = "0x00 - PLIC UX Interrupt Enable Register"]
    #[inline(always)]
    pub const fn uxint_enable(&self) -> &UXINT_ENABLE {
        &self.uxint_enable
    }
    #[doc = "0x04 - PLIC UX Interrupt Type Register"]
    #[inline(always)]
    pub const fn uxint_type(&self) -> &UXINT_TYPE {
        &self.uxint_type
    }
    #[doc = "0x08 - PLIC UX Interrupt Clear Register"]
    #[inline(always)]
    pub const fn uxint_clear(&self) -> &UXINT_CLEAR {
        &self.uxint_clear
    }
    #[doc = "0x0c - PLIC EMIP Status Register"]
    #[inline(always)]
    pub const fn euip_status(&self) -> &EUIP_STATUS {
        &self.euip_status
    }
    #[doc = "0x10..0x90 - PLIC UX Interrupt %s Priority Register"]
    #[inline(always)]
    pub const fn uxint_pri(&self, n: usize) -> &UXINT_PRI {
        &self.uxint_pri[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x10..0x90 - PLIC UX Interrupt %s Priority Register"]
    #[inline(always)]
    pub fn uxint_pri_iter(&self) -> impl Iterator<Item = &UXINT_PRI> {
        self.uxint_pri.iter()
    }
    #[doc = "0x10 - PLIC UX Interrupt 0 Priority Register"]
    #[inline(always)]
    pub const fn uxint0_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(0)
    }
    #[doc = "0x14 - PLIC UX Interrupt 1 Priority Register"]
    #[inline(always)]
    pub const fn uxint1_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(1)
    }
    #[doc = "0x18 - PLIC UX Interrupt 2 Priority Register"]
    #[inline(always)]
    pub const fn uxint2_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(2)
    }
    #[doc = "0x1c - PLIC UX Interrupt 3 Priority Register"]
    #[inline(always)]
    pub const fn uxint3_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(3)
    }
    #[doc = "0x20 - PLIC UX Interrupt 4 Priority Register"]
    #[inline(always)]
    pub const fn uxint4_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(4)
    }
    #[doc = "0x24 - PLIC UX Interrupt 5 Priority Register"]
    #[inline(always)]
    pub const fn uxint5_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(5)
    }
    #[doc = "0x28 - PLIC UX Interrupt 6 Priority Register"]
    #[inline(always)]
    pub const fn uxint6_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(6)
    }
    #[doc = "0x2c - PLIC UX Interrupt 7 Priority Register"]
    #[inline(always)]
    pub const fn uxint7_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(7)
    }
    #[doc = "0x30 - PLIC UX Interrupt 8 Priority Register"]
    #[inline(always)]
    pub const fn uxint8_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(8)
    }
    #[doc = "0x34 - PLIC UX Interrupt 9 Priority Register"]
    #[inline(always)]
    pub const fn uxint9_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(9)
    }
    #[doc = "0x38 - PLIC UX Interrupt 10 Priority Register"]
    #[inline(always)]
    pub const fn uxint10_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(10)
    }
    #[doc = "0x3c - PLIC UX Interrupt 11 Priority Register"]
    #[inline(always)]
    pub const fn uxint11_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(11)
    }
    #[doc = "0x40 - PLIC UX Interrupt 12 Priority Register"]
    #[inline(always)]
    pub const fn uxint12_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(12)
    }
    #[doc = "0x44 - PLIC UX Interrupt 13 Priority Register"]
    #[inline(always)]
    pub const fn uxint13_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(13)
    }
    #[doc = "0x48 - PLIC UX Interrupt 14 Priority Register"]
    #[inline(always)]
    pub const fn uxint14_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(14)
    }
    #[doc = "0x4c - PLIC UX Interrupt 15 Priority Register"]
    #[inline(always)]
    pub const fn uxint15_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(15)
    }
    #[doc = "0x50 - PLIC UX Interrupt 16 Priority Register"]
    #[inline(always)]
    pub const fn uxint16_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(16)
    }
    #[doc = "0x54 - PLIC UX Interrupt 17 Priority Register"]
    #[inline(always)]
    pub const fn uxint17_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(17)
    }
    #[doc = "0x58 - PLIC UX Interrupt 18 Priority Register"]
    #[inline(always)]
    pub const fn uxint18_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(18)
    }
    #[doc = "0x5c - PLIC UX Interrupt 19 Priority Register"]
    #[inline(always)]
    pub const fn uxint19_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(19)
    }
    #[doc = "0x60 - PLIC UX Interrupt 20 Priority Register"]
    #[inline(always)]
    pub const fn uxint20_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(20)
    }
    #[doc = "0x64 - PLIC UX Interrupt 21 Priority Register"]
    #[inline(always)]
    pub const fn uxint21_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(21)
    }
    #[doc = "0x68 - PLIC UX Interrupt 22 Priority Register"]
    #[inline(always)]
    pub const fn uxint22_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(22)
    }
    #[doc = "0x6c - PLIC UX Interrupt 23 Priority Register"]
    #[inline(always)]
    pub const fn uxint23_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(23)
    }
    #[doc = "0x70 - PLIC UX Interrupt 24 Priority Register"]
    #[inline(always)]
    pub const fn uxint24_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(24)
    }
    #[doc = "0x74 - PLIC UX Interrupt 25 Priority Register"]
    #[inline(always)]
    pub const fn uxint25_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(25)
    }
    #[doc = "0x78 - PLIC UX Interrupt 26 Priority Register"]
    #[inline(always)]
    pub const fn uxint26_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(26)
    }
    #[doc = "0x7c - PLIC UX Interrupt 27 Priority Register"]
    #[inline(always)]
    pub const fn uxint27_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(27)
    }
    #[doc = "0x80 - PLIC UX Interrupt 28 Priority Register"]
    #[inline(always)]
    pub const fn uxint28_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(28)
    }
    #[doc = "0x84 - PLIC UX Interrupt 29 Priority Register"]
    #[inline(always)]
    pub const fn uxint29_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(29)
    }
    #[doc = "0x88 - PLIC UX Interrupt 30 Priority Register"]
    #[inline(always)]
    pub const fn uxint30_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(30)
    }
    #[doc = "0x8c - PLIC UX Interrupt 31 Priority Register"]
    #[inline(always)]
    pub const fn uxint31_pri(&self) -> &UXINT_PRI {
        self.uxint_pri(31)
    }
    #[doc = "0x90 - PLIC UX Interrupt Threshold Register"]
    #[inline(always)]
    pub const fn uxint_thresh(&self) -> &UXINT_THRESH {
        &self.uxint_thresh
    }
    #[doc = "0x94 - PLIC UX Interrupt Claim Register"]
    #[inline(always)]
    pub const fn uxint_claim(&self) -> &UXINT_CLAIM {
        &self.uxint_claim
    }
}
#[doc = "UXINT_ENABLE (rw) register accessor: PLIC UX Interrupt Enable Register\n\nYou can [`read`](crate::Reg::read) this register and get [`uxint_enable::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uxint_enable::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@uxint_enable`] module"]
pub type UXINT_ENABLE = crate::Reg<uxint_enable::UXINT_ENABLE_SPEC>;
#[doc = "PLIC UX Interrupt Enable Register"]
pub mod uxint_enable;
#[doc = "UXINT_TYPE (rw) register accessor: PLIC UX Interrupt Type Register\n\nYou can [`read`](crate::Reg::read) this register and get [`uxint_type::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uxint_type::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@uxint_type`] module"]
pub type UXINT_TYPE = crate::Reg<uxint_type::UXINT_TYPE_SPEC>;
#[doc = "PLIC UX Interrupt Type Register"]
pub mod uxint_type;
#[doc = "UXINT_CLEAR (rw) register accessor: PLIC UX Interrupt Clear Register\n\nYou can [`read`](crate::Reg::read) this register and get [`uxint_clear::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uxint_clear::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@uxint_clear`] module"]
pub type UXINT_CLEAR = crate::Reg<uxint_clear::UXINT_CLEAR_SPEC>;
#[doc = "PLIC UX Interrupt Clear Register"]
pub mod uxint_clear;
#[doc = "EUIP_STATUS (r) register accessor: PLIC EMIP Status Register\n\nYou can [`read`](crate::Reg::read) this register and get [`euip_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@euip_status`] module"]
pub type EUIP_STATUS = crate::Reg<euip_status::EUIP_STATUS_SPEC>;
#[doc = "PLIC EMIP Status Register"]
pub mod euip_status;
#[doc = "UXINT_PRI (rw) register accessor: PLIC UX Interrupt %s Priority Register\n\nYou can [`read`](crate::Reg::read) this register and get [`uxint_pri::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uxint_pri::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@uxint_pri`] module"]
pub type UXINT_PRI = crate::Reg<uxint_pri::UXINT_PRI_SPEC>;
#[doc = "PLIC UX Interrupt %s Priority Register"]
pub mod uxint_pri;
#[doc = "UXINT_THRESH (rw) register accessor: PLIC UX Interrupt Threshold Register\n\nYou can [`read`](crate::Reg::read) this register and get [`uxint_thresh::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uxint_thresh::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@uxint_thresh`] module"]
pub type UXINT_THRESH = crate::Reg<uxint_thresh::UXINT_THRESH_SPEC>;
#[doc = "PLIC UX Interrupt Threshold Register"]
pub mod uxint_thresh;
#[doc = "UXINT_CLAIM (rw) register accessor: PLIC UX Interrupt Claim Register\n\nYou can [`read`](crate::Reg::read) this register and get [`uxint_claim::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uxint_claim::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@uxint_claim`] module"]
pub type UXINT_CLAIM = crate::Reg<uxint_claim::UXINT_CLAIM_SPEC>;
#[doc = "PLIC UX Interrupt Claim Register"]
pub mod uxint_claim;
