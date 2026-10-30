#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    msc_ctl: MscCtl,
    msc_rintf: MscRintf,
    msc_tintf: MscTintf,
    msc_rintmsk: MscRintmsk,
    msc_tintmsk: MscTintmsk,
    _reserved5: [u8; 0x38],
    msc_sccnt: MscSccnt,
    msc_msccnt: MscMsccnt,
    _reserved7: [u8; 0x14],
    msc_tgfcnt: MscTgfcnt,
    _reserved8: [u8; 0x28],
    msc_rfcecnt: MscRfcecnt,
    msc_rfaecnt: MscRfaecnt,
    _reserved10: [u8; 0x28],
    msc_rgufcnt: MscRgufcnt,
}
impl RegisterBlock {
    #[doc = "0x00 - Ethernet MSC control register (MSC_CTL)"]
    #[inline(always)]
    pub const fn msc_ctl(&self) -> &MscCtl {
        &self.msc_ctl
    }
    #[doc = "0x04 - Ethernet MSC receive interrupt flag register (MSC_RINTF)"]
    #[inline(always)]
    pub const fn msc_rintf(&self) -> &MscRintf {
        &self.msc_rintf
    }
    #[doc = "0x08 - Ethernet MSC transmit interrupt flag register (MSC_TINTF)"]
    #[inline(always)]
    pub const fn msc_tintf(&self) -> &MscTintf {
        &self.msc_tintf
    }
    #[doc = "0x0c - Ethernet MSC receive interrupt mask register (MSC_RINTMSK)"]
    #[inline(always)]
    pub const fn msc_rintmsk(&self) -> &MscRintmsk {
        &self.msc_rintmsk
    }
    #[doc = "0x10 - Ethernet MSC transmit interrupt mask register (MSC_TINTMSK)"]
    #[inline(always)]
    pub const fn msc_tintmsk(&self) -> &MscTintmsk {
        &self.msc_tintmsk
    }
    #[doc = "0x4c - Ethernet MSC transmitted good frames after a single collision counter"]
    #[inline(always)]
    pub const fn msc_sccnt(&self) -> &MscSccnt {
        &self.msc_sccnt
    }
    #[doc = "0x50 - Ethernet MSC transmitted good frames after more than a single collision"]
    #[inline(always)]
    pub const fn msc_msccnt(&self) -> &MscMsccnt {
        &self.msc_msccnt
    }
    #[doc = "0x68 - Ethernet MSC transmitted good frames counter register"]
    #[inline(always)]
    pub const fn msc_tgfcnt(&self) -> &MscTgfcnt {
        &self.msc_tgfcnt
    }
    #[doc = "0x94 - Ethernet MSC received frames with CRC error counter register"]
    #[inline(always)]
    pub const fn msc_rfcecnt(&self) -> &MscRfcecnt {
        &self.msc_rfcecnt
    }
    #[doc = "0x98 - Ethernet MSC received frames with alignment error counter register"]
    #[inline(always)]
    pub const fn msc_rfaecnt(&self) -> &MscRfaecnt {
        &self.msc_rfaecnt
    }
    #[doc = "0xc4 - MSC received good unicast frames counter register"]
    #[inline(always)]
    pub const fn msc_rgufcnt(&self) -> &MscRgufcnt {
        &self.msc_rgufcnt
    }
}
#[doc = "MSC_CTL (rw) register accessor: Ethernet MSC control register (MSC_CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`msc_ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@msc_ctl`]
module"]
#[doc(alias = "MSC_CTL")]
pub type MscCtl = crate::Reg<msc_ctl::MscCtlSpec>;
#[doc = "Ethernet MSC control register (MSC_CTL)"]
pub mod msc_ctl;
#[doc = "MSC_RINTF (r) register accessor: Ethernet MSC receive interrupt flag register (MSC_RINTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_rintf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@msc_rintf`]
module"]
#[doc(alias = "MSC_RINTF")]
pub type MscRintf = crate::Reg<msc_rintf::MscRintfSpec>;
#[doc = "Ethernet MSC receive interrupt flag register (MSC_RINTF)"]
pub mod msc_rintf;
#[doc = "MSC_TINTF (r) register accessor: Ethernet MSC transmit interrupt flag register (MSC_TINTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_tintf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@msc_tintf`]
module"]
#[doc(alias = "MSC_TINTF")]
pub type MscTintf = crate::Reg<msc_tintf::MscTintfSpec>;
#[doc = "Ethernet MSC transmit interrupt flag register (MSC_TINTF)"]
pub mod msc_tintf;
#[doc = "MSC_RINTMSK (rw) register accessor: Ethernet MSC receive interrupt mask register (MSC_RINTMSK)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_rintmsk::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`msc_rintmsk::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@msc_rintmsk`]
module"]
#[doc(alias = "MSC_RINTMSK")]
pub type MscRintmsk = crate::Reg<msc_rintmsk::MscRintmskSpec>;
#[doc = "Ethernet MSC receive interrupt mask register (MSC_RINTMSK)"]
pub mod msc_rintmsk;
#[doc = "MSC_TINTMSK (rw) register accessor: Ethernet MSC transmit interrupt mask register (MSC_TINTMSK)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_tintmsk::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`msc_tintmsk::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@msc_tintmsk`]
module"]
#[doc(alias = "MSC_TINTMSK")]
pub type MscTintmsk = crate::Reg<msc_tintmsk::MscTintmskSpec>;
#[doc = "Ethernet MSC transmit interrupt mask register (MSC_TINTMSK)"]
pub mod msc_tintmsk;
#[doc = "MSC_SCCNT (r) register accessor: Ethernet MSC transmitted good frames after a single collision counter\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_sccnt::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@msc_sccnt`]
module"]
#[doc(alias = "MSC_SCCNT")]
pub type MscSccnt = crate::Reg<msc_sccnt::MscSccntSpec>;
#[doc = "Ethernet MSC transmitted good frames after a single collision counter"]
pub mod msc_sccnt;
#[doc = "MSC_MSCCNT (r) register accessor: Ethernet MSC transmitted good frames after more than a single collision\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_msccnt::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@msc_msccnt`]
module"]
#[doc(alias = "MSC_MSCCNT")]
pub type MscMsccnt = crate::Reg<msc_msccnt::MscMsccntSpec>;
#[doc = "Ethernet MSC transmitted good frames after more than a single collision"]
pub mod msc_msccnt;
#[doc = "MSC_TGFCNT (r) register accessor: Ethernet MSC transmitted good frames counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_tgfcnt::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@msc_tgfcnt`]
module"]
#[doc(alias = "MSC_TGFCNT")]
pub type MscTgfcnt = crate::Reg<msc_tgfcnt::MscTgfcntSpec>;
#[doc = "Ethernet MSC transmitted good frames counter register"]
pub mod msc_tgfcnt;
#[doc = "MSC_RFCECNT (r) register accessor: Ethernet MSC received frames with CRC error counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_rfcecnt::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@msc_rfcecnt`]
module"]
#[doc(alias = "MSC_RFCECNT")]
pub type MscRfcecnt = crate::Reg<msc_rfcecnt::MscRfcecntSpec>;
#[doc = "Ethernet MSC received frames with CRC error counter register"]
pub mod msc_rfcecnt;
#[doc = "MSC_RFAECNT (r) register accessor: Ethernet MSC received frames with alignment error counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_rfaecnt::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@msc_rfaecnt`]
module"]
#[doc(alias = "MSC_RFAECNT")]
pub type MscRfaecnt = crate::Reg<msc_rfaecnt::MscRfaecntSpec>;
#[doc = "Ethernet MSC received frames with alignment error counter register"]
pub mod msc_rfaecnt;
#[doc = "MSC_RGUFCNT (r) register accessor: MSC received good unicast frames counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`msc_rgufcnt::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@msc_rgufcnt`]
module"]
#[doc(alias = "MSC_RGUFCNT")]
pub type MscRgufcnt = crate::Reg<msc_rgufcnt::MscRgufcntSpec>;
#[doc = "MSC received good unicast frames counter register"]
pub mod msc_rgufcnt;
