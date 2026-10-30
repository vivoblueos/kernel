#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    hctl: Hctl,
    hft: Hft,
    hfinfr: Hfinfr,
    _reserved3: [u8; 0x04],
    hptfqstat: Hptfqstat,
    hachint: Hachint,
    hachinten: Hachinten,
    _reserved6: [u8; 0x24],
    hpcs: Hpcs,
    _reserved7: [u8; 0xbc],
    hch0ctl: Hch0ctl,
    _reserved8: [u8; 0x04],
    hch0intf: Hch0intf,
    hch0inten: Hch0inten,
    hch0len: Hch0len,
    hch0dmaaddr: Hch0dmaaddr,
    _reserved12: [u8; 0x08],
    hch1ctl: Hch1ctl,
    _reserved13: [u8; 0x04],
    hch1intf: Hch1intf,
    hch1inten: Hch1inten,
    hch1len: Hch1len,
    hch1dmaaddr: Hch1dmaaddr,
    _reserved17: [u8; 0x08],
    hch2ctl: Hch2ctl,
    _reserved18: [u8; 0x04],
    hch2intf: Hch2intf,
    hch2inten: Hch2inten,
    hch2len: Hch2len,
    hch2dmaaddr: Hch2dmaaddr,
    _reserved22: [u8; 0x08],
    hch3ctl: Hch3ctl,
    _reserved23: [u8; 0x04],
    hch3intf: Hch3intf,
    hch3inten: Hch3inten,
    hch3len: Hch3len,
    hch3dmaaddr: Hch3dmaaddr,
    _reserved27: [u8; 0x08],
    hch4ctl: Hch4ctl,
    _reserved28: [u8; 0x04],
    hch4intf: Hch4intf,
    hch4inten: Hch4inten,
    hch4len: Hch4len,
    hch4dmaaddr: Hch4dmaaddr,
    _reserved32: [u8; 0x08],
    hch5ctl: Hch5ctl,
    _reserved33: [u8; 0x04],
    hch5intf: Hch5intf,
    hch5inten: Hch5inten,
    hch5len: Hch5len,
    hch5dmaaddr: Hch5dmaaddr,
    _reserved37: [u8; 0x08],
    hch6ctl: Hch6ctl,
    _reserved38: [u8; 0x04],
    hch6intf: Hch6intf,
    hch6inten: Hch6inten,
    hch6len: Hch6len,
    hch6dmaaddr: Hch6dmaaddr,
    _reserved42: [u8; 0x08],
    hch7ctl: Hch7ctl,
    _reserved43: [u8; 0x04],
    hch7intf: Hch7intf,
    hch7inten: Hch7inten,
    hch7len: Hch7len,
    hch7dmaaddr: Hch7dmaaddr,
    _reserved47: [u8; 0x08],
    hch8ctl: Hch8ctl,
    _reserved48: [u8; 0x04],
    hch8intf: Hch8intf,
    hch8inten: Hch8inten,
    hch8len: Hch8len,
    hch8dmaaddr: Hch8dmaaddr,
    _reserved52: [u8; 0x08],
    hch9ctl: Hch9ctl,
    _reserved53: [u8; 0x04],
    hch9intf: Hch9intf,
    hch9inten: Hch9inten,
    hch9len: Hch9len,
    hch9dmaaddr: Hch9dmaaddr,
    _reserved57: [u8; 0x08],
    hch10ctl: Hch10ctl,
    _reserved58: [u8; 0x04],
    hch10intf: Hch10intf,
    hch10inten: Hch10inten,
    hch10len: Hch10len,
    hch10dmaaddr: Hch10dmaaddr,
    _reserved62: [u8; 0x08],
    hch11ctl: Hch11ctl,
    _reserved63: [u8; 0x04],
    hch11intf: Hch11intf,
    hch11inten: Hch11inten,
    hch11len: Hch11len,
    hch11dmaaddr: Hch11dmaaddr,
}
impl RegisterBlock {
    #[doc = "0x00 - host configuration register (HCTL)"]
    #[inline(always)]
    pub const fn hctl(&self) -> &Hctl {
        &self.hctl
    }
    #[doc = "0x04 - Host frame interval register"]
    #[inline(always)]
    pub const fn hft(&self) -> &Hft {
        &self.hft
    }
    #[doc = "0x08 - OTG_FS host frame number/frame time remaining register (HFINFR)"]
    #[inline(always)]
    pub const fn hfinfr(&self) -> &Hfinfr {
        &self.hfinfr
    }
    #[doc = "0x10 - Host periodic transmit FIFO/queue status register (HPTFQSTAT)"]
    #[inline(always)]
    pub const fn hptfqstat(&self) -> &Hptfqstat {
        &self.hptfqstat
    }
    #[doc = "0x14 - Host all channels interrupt register"]
    #[inline(always)]
    pub const fn hachint(&self) -> &Hachint {
        &self.hachint
    }
    #[doc = "0x18 - host all channels interrupt mask register"]
    #[inline(always)]
    pub const fn hachinten(&self) -> &Hachinten {
        &self.hachinten
    }
    #[doc = "0x40 - Host port control and status register (USBFS_HPCS)"]
    #[inline(always)]
    pub const fn hpcs(&self) -> &Hpcs {
        &self.hpcs
    }
    #[doc = "0x100 - host channel-0 characteristics register (HCH0CTL)"]
    #[inline(always)]
    pub const fn hch0ctl(&self) -> &Hch0ctl {
        &self.hch0ctl
    }
    #[doc = "0x108 - host channel-0 interrupt register (USBHS_HCHxINTF)"]
    #[inline(always)]
    pub const fn hch0intf(&self) -> &Hch0intf {
        &self.hch0intf
    }
    #[doc = "0x10c - host channel-0 interrupt enable register (HCH0INTEN)"]
    #[inline(always)]
    pub const fn hch0inten(&self) -> &Hch0inten {
        &self.hch0inten
    }
    #[doc = "0x110 - host channel-0 transfer length register"]
    #[inline(always)]
    pub const fn hch0len(&self) -> &Hch0len {
        &self.hch0len
    }
    #[doc = "0x114 - Host channel 0 DMA address register"]
    #[inline(always)]
    pub const fn hch0dmaaddr(&self) -> &Hch0dmaaddr {
        &self.hch0dmaaddr
    }
    #[doc = "0x120 - host channel-1 characteristics register (HCH1CTL)"]
    #[inline(always)]
    pub const fn hch1ctl(&self) -> &Hch1ctl {
        &self.hch1ctl
    }
    #[doc = "0x128 - host channel-1 interrupt register (HCH1INTF)"]
    #[inline(always)]
    pub const fn hch1intf(&self) -> &Hch1intf {
        &self.hch1intf
    }
    #[doc = "0x12c - host channel-1 interrupt enable register (HCH1INTEN)"]
    #[inline(always)]
    pub const fn hch1inten(&self) -> &Hch1inten {
        &self.hch1inten
    }
    #[doc = "0x130 - host channel-1 transfer length register"]
    #[inline(always)]
    pub const fn hch1len(&self) -> &Hch1len {
        &self.hch1len
    }
    #[doc = "0x134 - Host channel 1 DMA address register"]
    #[inline(always)]
    pub const fn hch1dmaaddr(&self) -> &Hch1dmaaddr {
        &self.hch1dmaaddr
    }
    #[doc = "0x140 - host channel-2 characteristics register (HCH2CTL)"]
    #[inline(always)]
    pub const fn hch2ctl(&self) -> &Hch2ctl {
        &self.hch2ctl
    }
    #[doc = "0x148 - host channel-2 interrupt register (HCH2INTF)"]
    #[inline(always)]
    pub const fn hch2intf(&self) -> &Hch2intf {
        &self.hch2intf
    }
    #[doc = "0x14c - host channel-2 interrupt enable register (HCH2INTEN)"]
    #[inline(always)]
    pub const fn hch2inten(&self) -> &Hch2inten {
        &self.hch2inten
    }
    #[doc = "0x150 - host channel-2 transfer length register"]
    #[inline(always)]
    pub const fn hch2len(&self) -> &Hch2len {
        &self.hch2len
    }
    #[doc = "0x154 - Host channel 2 DMA address register"]
    #[inline(always)]
    pub const fn hch2dmaaddr(&self) -> &Hch2dmaaddr {
        &self.hch2dmaaddr
    }
    #[doc = "0x160 - host channel-3 characteristics register (HCH3CTL)"]
    #[inline(always)]
    pub const fn hch3ctl(&self) -> &Hch3ctl {
        &self.hch3ctl
    }
    #[doc = "0x168 - host channel-3 interrupt register (HCH3INTF)"]
    #[inline(always)]
    pub const fn hch3intf(&self) -> &Hch3intf {
        &self.hch3intf
    }
    #[doc = "0x16c - host channel-3 interrupt enable register (HCH3INTEN)"]
    #[inline(always)]
    pub const fn hch3inten(&self) -> &Hch3inten {
        &self.hch3inten
    }
    #[doc = "0x170 - host channel-3 transfer length register"]
    #[inline(always)]
    pub const fn hch3len(&self) -> &Hch3len {
        &self.hch3len
    }
    #[doc = "0x174 - Host channel 3 DMA address register"]
    #[inline(always)]
    pub const fn hch3dmaaddr(&self) -> &Hch3dmaaddr {
        &self.hch3dmaaddr
    }
    #[doc = "0x180 - host channel-4 characteristics register (HCH4CTL)"]
    #[inline(always)]
    pub const fn hch4ctl(&self) -> &Hch4ctl {
        &self.hch4ctl
    }
    #[doc = "0x188 - host channel-4 interrupt register (HCH4INTF)"]
    #[inline(always)]
    pub const fn hch4intf(&self) -> &Hch4intf {
        &self.hch4intf
    }
    #[doc = "0x18c - host channel-4 interrupt enable register (HCH4INTEN)"]
    #[inline(always)]
    pub const fn hch4inten(&self) -> &Hch4inten {
        &self.hch4inten
    }
    #[doc = "0x190 - host channel-4 transfer length register"]
    #[inline(always)]
    pub const fn hch4len(&self) -> &Hch4len {
        &self.hch4len
    }
    #[doc = "0x194 - Host channel 4 DMA address register"]
    #[inline(always)]
    pub const fn hch4dmaaddr(&self) -> &Hch4dmaaddr {
        &self.hch4dmaaddr
    }
    #[doc = "0x1a0 - host channel-5 characteristics register (HCH5CTL)"]
    #[inline(always)]
    pub const fn hch5ctl(&self) -> &Hch5ctl {
        &self.hch5ctl
    }
    #[doc = "0x1a8 - host channel-5 interrupt register (HCH5INTF)"]
    #[inline(always)]
    pub const fn hch5intf(&self) -> &Hch5intf {
        &self.hch5intf
    }
    #[doc = "0x1ac - host channel-5 interrupt enable register (HCH5INTEN)"]
    #[inline(always)]
    pub const fn hch5inten(&self) -> &Hch5inten {
        &self.hch5inten
    }
    #[doc = "0x1b0 - host channel-5 transfer length register"]
    #[inline(always)]
    pub const fn hch5len(&self) -> &Hch5len {
        &self.hch5len
    }
    #[doc = "0x1b4 - Host channel 5 DMA address register"]
    #[inline(always)]
    pub const fn hch5dmaaddr(&self) -> &Hch5dmaaddr {
        &self.hch5dmaaddr
    }
    #[doc = "0x1c0 - host channel-6 characteristics register (HCH6CTL)"]
    #[inline(always)]
    pub const fn hch6ctl(&self) -> &Hch6ctl {
        &self.hch6ctl
    }
    #[doc = "0x1c8 - host channel-6 interrupt register (HCH6INTF)"]
    #[inline(always)]
    pub const fn hch6intf(&self) -> &Hch6intf {
        &self.hch6intf
    }
    #[doc = "0x1cc - host channel-6 interrupt enable register (HCH6INTEN)"]
    #[inline(always)]
    pub const fn hch6inten(&self) -> &Hch6inten {
        &self.hch6inten
    }
    #[doc = "0x1d0 - host channel-6 transfer length register"]
    #[inline(always)]
    pub const fn hch6len(&self) -> &Hch6len {
        &self.hch6len
    }
    #[doc = "0x1d4 - Host channel 6 DMA address register"]
    #[inline(always)]
    pub const fn hch6dmaaddr(&self) -> &Hch6dmaaddr {
        &self.hch6dmaaddr
    }
    #[doc = "0x1e0 - host channel-7 characteristics register (HCH7CTL)"]
    #[inline(always)]
    pub const fn hch7ctl(&self) -> &Hch7ctl {
        &self.hch7ctl
    }
    #[doc = "0x1e8 - host channel-7 interrupt register (HCH7INTF)"]
    #[inline(always)]
    pub const fn hch7intf(&self) -> &Hch7intf {
        &self.hch7intf
    }
    #[doc = "0x1ec - host channel-7 interrupt enable register (HCH7INTEN)"]
    #[inline(always)]
    pub const fn hch7inten(&self) -> &Hch7inten {
        &self.hch7inten
    }
    #[doc = "0x1f0 - host channel-7 transfer length register"]
    #[inline(always)]
    pub const fn hch7len(&self) -> &Hch7len {
        &self.hch7len
    }
    #[doc = "0x1f4 - Host channel 7 DMA address register"]
    #[inline(always)]
    pub const fn hch7dmaaddr(&self) -> &Hch7dmaaddr {
        &self.hch7dmaaddr
    }
    #[doc = "0x200 - host channel-8 characteristics register (HCH8CTL)"]
    #[inline(always)]
    pub const fn hch8ctl(&self) -> &Hch8ctl {
        &self.hch8ctl
    }
    #[doc = "0x208 - host channel-8 interrupt register (HCH8INTF)"]
    #[inline(always)]
    pub const fn hch8intf(&self) -> &Hch8intf {
        &self.hch8intf
    }
    #[doc = "0x20c - host channel-8 interrupt enable register (HCH7INTEN)"]
    #[inline(always)]
    pub const fn hch8inten(&self) -> &Hch8inten {
        &self.hch8inten
    }
    #[doc = "0x210 - host channel-8 transfer length register"]
    #[inline(always)]
    pub const fn hch8len(&self) -> &Hch8len {
        &self.hch8len
    }
    #[doc = "0x214 - Host channel 8 DMA address register"]
    #[inline(always)]
    pub const fn hch8dmaaddr(&self) -> &Hch8dmaaddr {
        &self.hch8dmaaddr
    }
    #[doc = "0x220 - host channel-9 characteristics register (HCH9CTL)"]
    #[inline(always)]
    pub const fn hch9ctl(&self) -> &Hch9ctl {
        &self.hch9ctl
    }
    #[doc = "0x228 - host channel-9 interrupt register (HCH9INTF)"]
    #[inline(always)]
    pub const fn hch9intf(&self) -> &Hch9intf {
        &self.hch9intf
    }
    #[doc = "0x22c - host channel-9 interrupt enable register (HCH9INTEN)"]
    #[inline(always)]
    pub const fn hch9inten(&self) -> &Hch9inten {
        &self.hch9inten
    }
    #[doc = "0x230 - host channel-9 transfer length register"]
    #[inline(always)]
    pub const fn hch9len(&self) -> &Hch9len {
        &self.hch9len
    }
    #[doc = "0x234 - Host channel 9 DMA address register"]
    #[inline(always)]
    pub const fn hch9dmaaddr(&self) -> &Hch9dmaaddr {
        &self.hch9dmaaddr
    }
    #[doc = "0x240 - host channel-10 characteristics register (HCH10CTL)"]
    #[inline(always)]
    pub const fn hch10ctl(&self) -> &Hch10ctl {
        &self.hch10ctl
    }
    #[doc = "0x248 - host channel-10 interrupt register (HCH10INTF)"]
    #[inline(always)]
    pub const fn hch10intf(&self) -> &Hch10intf {
        &self.hch10intf
    }
    #[doc = "0x24c - host channel-10 interrupt enable register (HCH10INTEN)"]
    #[inline(always)]
    pub const fn hch10inten(&self) -> &Hch10inten {
        &self.hch10inten
    }
    #[doc = "0x250 - host channel-10 transfer length register"]
    #[inline(always)]
    pub const fn hch10len(&self) -> &Hch10len {
        &self.hch10len
    }
    #[doc = "0x254 - Host channel 10 DMA address register"]
    #[inline(always)]
    pub const fn hch10dmaaddr(&self) -> &Hch10dmaaddr {
        &self.hch10dmaaddr
    }
    #[doc = "0x260 - host channel-11 characteristics register (HCH11CTL)"]
    #[inline(always)]
    pub const fn hch11ctl(&self) -> &Hch11ctl {
        &self.hch11ctl
    }
    #[doc = "0x268 - host channel-11 interrupt register (HCH11INTF)"]
    #[inline(always)]
    pub const fn hch11intf(&self) -> &Hch11intf {
        &self.hch11intf
    }
    #[doc = "0x26c - host channel-11 interrupt enable register (HCH11INTEN)"]
    #[inline(always)]
    pub const fn hch11inten(&self) -> &Hch11inten {
        &self.hch11inten
    }
    #[doc = "0x270 - host channel-11 transfer length register"]
    #[inline(always)]
    pub const fn hch11len(&self) -> &Hch11len {
        &self.hch11len
    }
    #[doc = "0x274 - Host channel 11 DMA address register"]
    #[inline(always)]
    pub const fn hch11dmaaddr(&self) -> &Hch11dmaaddr {
        &self.hch11dmaaddr
    }
}
#[doc = "HCTL (rw) register accessor: host configuration register (HCTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hctl`]
module"]
#[doc(alias = "HCTL")]
pub type Hctl = crate::Reg<hctl::HctlSpec>;
#[doc = "host configuration register (HCTL)"]
pub mod hctl;
#[doc = "HFT (rw) register accessor: Host frame interval register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hft::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hft::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hft`]
module"]
#[doc(alias = "HFT")]
pub type Hft = crate::Reg<hft::HftSpec>;
#[doc = "Host frame interval register"]
pub mod hft;
#[doc = "HFINFR (r) register accessor: OTG_FS host frame number/frame time remaining register (HFINFR)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hfinfr::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hfinfr`]
module"]
#[doc(alias = "HFINFR")]
pub type Hfinfr = crate::Reg<hfinfr::HfinfrSpec>;
#[doc = "OTG_FS host frame number/frame time remaining register (HFINFR)"]
pub mod hfinfr;
#[doc = "HPTFQSTAT (r) register accessor: Host periodic transmit FIFO/queue status register (HPTFQSTAT)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hptfqstat::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hptfqstat`]
module"]
#[doc(alias = "HPTFQSTAT")]
pub type Hptfqstat = crate::Reg<hptfqstat::HptfqstatSpec>;
#[doc = "Host periodic transmit FIFO/queue status register (HPTFQSTAT)"]
pub mod hptfqstat;
#[doc = "HACHINT (r) register accessor: Host all channels interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hachint::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hachint`]
module"]
#[doc(alias = "HACHINT")]
pub type Hachint = crate::Reg<hachint::HachintSpec>;
#[doc = "Host all channels interrupt register"]
pub mod hachint;
#[doc = "HACHINTEN (rw) register accessor: host all channels interrupt mask register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hachinten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hachinten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hachinten`]
module"]
#[doc(alias = "HACHINTEN")]
pub type Hachinten = crate::Reg<hachinten::HachintenSpec>;
#[doc = "host all channels interrupt mask register"]
pub mod hachinten;
#[doc = "HPCS (rw) register accessor: Host port control and status register (USBFS_HPCS)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hpcs::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hpcs::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hpcs`]
module"]
#[doc(alias = "HPCS")]
pub type Hpcs = crate::Reg<hpcs::HpcsSpec>;
#[doc = "Host port control and status register (USBFS_HPCS)"]
pub mod hpcs;
#[doc = "HCH0CTL (rw) register accessor: host channel-0 characteristics register (HCH0CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch0ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch0ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch0ctl`]
module"]
#[doc(alias = "HCH0CTL")]
pub type Hch0ctl = crate::Reg<hch0ctl::Hch0ctlSpec>;
#[doc = "host channel-0 characteristics register (HCH0CTL)"]
pub mod hch0ctl;
#[doc = "HCH1CTL (rw) register accessor: host channel-1 characteristics register (HCH1CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch1ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch1ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch1ctl`]
module"]
#[doc(alias = "HCH1CTL")]
pub type Hch1ctl = crate::Reg<hch1ctl::Hch1ctlSpec>;
#[doc = "host channel-1 characteristics register (HCH1CTL)"]
pub mod hch1ctl;
#[doc = "HCH2CTL (rw) register accessor: host channel-2 characteristics register (HCH2CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch2ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch2ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch2ctl`]
module"]
#[doc(alias = "HCH2CTL")]
pub type Hch2ctl = crate::Reg<hch2ctl::Hch2ctlSpec>;
#[doc = "host channel-2 characteristics register (HCH2CTL)"]
pub mod hch2ctl;
#[doc = "HCH3CTL (rw) register accessor: host channel-3 characteristics register (HCH3CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch3ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch3ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch3ctl`]
module"]
#[doc(alias = "HCH3CTL")]
pub type Hch3ctl = crate::Reg<hch3ctl::Hch3ctlSpec>;
#[doc = "host channel-3 characteristics register (HCH3CTL)"]
pub mod hch3ctl;
#[doc = "HCH4CTL (rw) register accessor: host channel-4 characteristics register (HCH4CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch4ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch4ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch4ctl`]
module"]
#[doc(alias = "HCH4CTL")]
pub type Hch4ctl = crate::Reg<hch4ctl::Hch4ctlSpec>;
#[doc = "host channel-4 characteristics register (HCH4CTL)"]
pub mod hch4ctl;
#[doc = "HCH5CTL (rw) register accessor: host channel-5 characteristics register (HCH5CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch5ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch5ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch5ctl`]
module"]
#[doc(alias = "HCH5CTL")]
pub type Hch5ctl = crate::Reg<hch5ctl::Hch5ctlSpec>;
#[doc = "host channel-5 characteristics register (HCH5CTL)"]
pub mod hch5ctl;
#[doc = "HCH6CTL (rw) register accessor: host channel-6 characteristics register (HCH6CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch6ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch6ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch6ctl`]
module"]
#[doc(alias = "HCH6CTL")]
pub type Hch6ctl = crate::Reg<hch6ctl::Hch6ctlSpec>;
#[doc = "host channel-6 characteristics register (HCH6CTL)"]
pub mod hch6ctl;
#[doc = "HCH7CTL (rw) register accessor: host channel-7 characteristics register (HCH7CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch7ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch7ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch7ctl`]
module"]
#[doc(alias = "HCH7CTL")]
pub type Hch7ctl = crate::Reg<hch7ctl::Hch7ctlSpec>;
#[doc = "host channel-7 characteristics register (HCH7CTL)"]
pub mod hch7ctl;
#[doc = "HCH8CTL (rw) register accessor: host channel-8 characteristics register (HCH8CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch8ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch8ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch8ctl`]
module"]
#[doc(alias = "HCH8CTL")]
pub type Hch8ctl = crate::Reg<hch8ctl::Hch8ctlSpec>;
#[doc = "host channel-8 characteristics register (HCH8CTL)"]
pub mod hch8ctl;
#[doc = "HCH9CTL (rw) register accessor: host channel-9 characteristics register (HCH9CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch9ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch9ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch9ctl`]
module"]
#[doc(alias = "HCH9CTL")]
pub type Hch9ctl = crate::Reg<hch9ctl::Hch9ctlSpec>;
#[doc = "host channel-9 characteristics register (HCH9CTL)"]
pub mod hch9ctl;
#[doc = "HCH10CTL (rw) register accessor: host channel-10 characteristics register (HCH10CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch10ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch10ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch10ctl`]
module"]
#[doc(alias = "HCH10CTL")]
pub type Hch10ctl = crate::Reg<hch10ctl::Hch10ctlSpec>;
#[doc = "host channel-10 characteristics register (HCH10CTL)"]
pub mod hch10ctl;
#[doc = "HCH11CTL (rw) register accessor: host channel-11 characteristics register (HCH11CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch11ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch11ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch11ctl`]
module"]
#[doc(alias = "HCH11CTL")]
pub type Hch11ctl = crate::Reg<hch11ctl::Hch11ctlSpec>;
#[doc = "host channel-11 characteristics register (HCH11CTL)"]
pub mod hch11ctl;
#[doc = "HCH0INTF (rw) register accessor: host channel-0 interrupt register (USBHS_HCHxINTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch0intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch0intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch0intf`]
module"]
#[doc(alias = "HCH0INTF")]
pub type Hch0intf = crate::Reg<hch0intf::Hch0intfSpec>;
#[doc = "host channel-0 interrupt register (USBHS_HCHxINTF)"]
pub mod hch0intf;
#[doc = "HCH1INTF (rw) register accessor: host channel-1 interrupt register (HCH1INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch1intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch1intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch1intf`]
module"]
#[doc(alias = "HCH1INTF")]
pub type Hch1intf = crate::Reg<hch1intf::Hch1intfSpec>;
#[doc = "host channel-1 interrupt register (HCH1INTF)"]
pub mod hch1intf;
#[doc = "HCH2INTF (rw) register accessor: host channel-2 interrupt register (HCH2INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch2intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch2intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch2intf`]
module"]
#[doc(alias = "HCH2INTF")]
pub type Hch2intf = crate::Reg<hch2intf::Hch2intfSpec>;
#[doc = "host channel-2 interrupt register (HCH2INTF)"]
pub mod hch2intf;
#[doc = "HCH3INTF (rw) register accessor: host channel-3 interrupt register (HCH3INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch3intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch3intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch3intf`]
module"]
#[doc(alias = "HCH3INTF")]
pub type Hch3intf = crate::Reg<hch3intf::Hch3intfSpec>;
#[doc = "host channel-3 interrupt register (HCH3INTF)"]
pub mod hch3intf;
#[doc = "HCH4INTF (rw) register accessor: host channel-4 interrupt register (HCH4INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch4intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch4intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch4intf`]
module"]
#[doc(alias = "HCH4INTF")]
pub type Hch4intf = crate::Reg<hch4intf::Hch4intfSpec>;
#[doc = "host channel-4 interrupt register (HCH4INTF)"]
pub mod hch4intf;
#[doc = "HCH5INTF (rw) register accessor: host channel-5 interrupt register (HCH5INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch5intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch5intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch5intf`]
module"]
#[doc(alias = "HCH5INTF")]
pub type Hch5intf = crate::Reg<hch5intf::Hch5intfSpec>;
#[doc = "host channel-5 interrupt register (HCH5INTF)"]
pub mod hch5intf;
#[doc = "HCH6INTF (rw) register accessor: host channel-6 interrupt register (HCH6INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch6intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch6intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch6intf`]
module"]
#[doc(alias = "HCH6INTF")]
pub type Hch6intf = crate::Reg<hch6intf::Hch6intfSpec>;
#[doc = "host channel-6 interrupt register (HCH6INTF)"]
pub mod hch6intf;
#[doc = "HCH7INTF (rw) register accessor: host channel-7 interrupt register (HCH7INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch7intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch7intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch7intf`]
module"]
#[doc(alias = "HCH7INTF")]
pub type Hch7intf = crate::Reg<hch7intf::Hch7intfSpec>;
#[doc = "host channel-7 interrupt register (HCH7INTF)"]
pub mod hch7intf;
#[doc = "HCH8INTF (rw) register accessor: host channel-8 interrupt register (HCH8INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch8intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch8intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch8intf`]
module"]
#[doc(alias = "HCH8INTF")]
pub type Hch8intf = crate::Reg<hch8intf::Hch8intfSpec>;
#[doc = "host channel-8 interrupt register (HCH8INTF)"]
pub mod hch8intf;
#[doc = "HCH9INTF (rw) register accessor: host channel-9 interrupt register (HCH9INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch9intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch9intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch9intf`]
module"]
#[doc(alias = "HCH9INTF")]
pub type Hch9intf = crate::Reg<hch9intf::Hch9intfSpec>;
#[doc = "host channel-9 interrupt register (HCH9INTF)"]
pub mod hch9intf;
#[doc = "HCH10INTF (rw) register accessor: host channel-10 interrupt register (HCH10INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch10intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch10intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch10intf`]
module"]
#[doc(alias = "HCH10INTF")]
pub type Hch10intf = crate::Reg<hch10intf::Hch10intfSpec>;
#[doc = "host channel-10 interrupt register (HCH10INTF)"]
pub mod hch10intf;
#[doc = "HCH11INTF (rw) register accessor: host channel-11 interrupt register (HCH11INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch11intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch11intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch11intf`]
module"]
#[doc(alias = "HCH11INTF")]
pub type Hch11intf = crate::Reg<hch11intf::Hch11intfSpec>;
#[doc = "host channel-11 interrupt register (HCH11INTF)"]
pub mod hch11intf;
#[doc = "HCH0INTEN (rw) register accessor: host channel-0 interrupt enable register (HCH0INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch0inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch0inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch0inten`]
module"]
#[doc(alias = "HCH0INTEN")]
pub type Hch0inten = crate::Reg<hch0inten::Hch0intenSpec>;
#[doc = "host channel-0 interrupt enable register (HCH0INTEN)"]
pub mod hch0inten;
#[doc = "HCH1INTEN (rw) register accessor: host channel-1 interrupt enable register (HCH1INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch1inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch1inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch1inten`]
module"]
#[doc(alias = "HCH1INTEN")]
pub type Hch1inten = crate::Reg<hch1inten::Hch1intenSpec>;
#[doc = "host channel-1 interrupt enable register (HCH1INTEN)"]
pub mod hch1inten;
#[doc = "HCH2INTEN (rw) register accessor: host channel-2 interrupt enable register (HCH2INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch2inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch2inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch2inten`]
module"]
#[doc(alias = "HCH2INTEN")]
pub type Hch2inten = crate::Reg<hch2inten::Hch2intenSpec>;
#[doc = "host channel-2 interrupt enable register (HCH2INTEN)"]
pub mod hch2inten;
#[doc = "HCH3INTEN (rw) register accessor: host channel-3 interrupt enable register (HCH3INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch3inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch3inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch3inten`]
module"]
#[doc(alias = "HCH3INTEN")]
pub type Hch3inten = crate::Reg<hch3inten::Hch3intenSpec>;
#[doc = "host channel-3 interrupt enable register (HCH3INTEN)"]
pub mod hch3inten;
#[doc = "HCH4INTEN (rw) register accessor: host channel-4 interrupt enable register (HCH4INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch4inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch4inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch4inten`]
module"]
#[doc(alias = "HCH4INTEN")]
pub type Hch4inten = crate::Reg<hch4inten::Hch4intenSpec>;
#[doc = "host channel-4 interrupt enable register (HCH4INTEN)"]
pub mod hch4inten;
#[doc = "HCH5INTEN (rw) register accessor: host channel-5 interrupt enable register (HCH5INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch5inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch5inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch5inten`]
module"]
#[doc(alias = "HCH5INTEN")]
pub type Hch5inten = crate::Reg<hch5inten::Hch5intenSpec>;
#[doc = "host channel-5 interrupt enable register (HCH5INTEN)"]
pub mod hch5inten;
#[doc = "HCH6INTEN (rw) register accessor: host channel-6 interrupt enable register (HCH6INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch6inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch6inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch6inten`]
module"]
#[doc(alias = "HCH6INTEN")]
pub type Hch6inten = crate::Reg<hch6inten::Hch6intenSpec>;
#[doc = "host channel-6 interrupt enable register (HCH6INTEN)"]
pub mod hch6inten;
#[doc = "HCH7INTEN (rw) register accessor: host channel-7 interrupt enable register (HCH7INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch7inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch7inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch7inten`]
module"]
#[doc(alias = "HCH7INTEN")]
pub type Hch7inten = crate::Reg<hch7inten::Hch7intenSpec>;
#[doc = "host channel-7 interrupt enable register (HCH7INTEN)"]
pub mod hch7inten;
#[doc = "HCH8INTEN (rw) register accessor: host channel-8 interrupt enable register (HCH7INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch8inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch8inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch8inten`]
module"]
#[doc(alias = "HCH8INTEN")]
pub type Hch8inten = crate::Reg<hch8inten::Hch8intenSpec>;
#[doc = "host channel-8 interrupt enable register (HCH7INTEN)"]
pub mod hch8inten;
#[doc = "HCH9INTEN (rw) register accessor: host channel-9 interrupt enable register (HCH9INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch9inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch9inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch9inten`]
module"]
#[doc(alias = "HCH9INTEN")]
pub type Hch9inten = crate::Reg<hch9inten::Hch9intenSpec>;
#[doc = "host channel-9 interrupt enable register (HCH9INTEN)"]
pub mod hch9inten;
#[doc = "HCH10INTEN (rw) register accessor: host channel-10 interrupt enable register (HCH10INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch10inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch10inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch10inten`]
module"]
#[doc(alias = "HCH10INTEN")]
pub type Hch10inten = crate::Reg<hch10inten::Hch10intenSpec>;
#[doc = "host channel-10 interrupt enable register (HCH10INTEN)"]
pub mod hch10inten;
#[doc = "HCH11INTEN (rw) register accessor: host channel-11 interrupt enable register (HCH11INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch11inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch11inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch11inten`]
module"]
#[doc(alias = "HCH11INTEN")]
pub type Hch11inten = crate::Reg<hch11inten::Hch11intenSpec>;
#[doc = "host channel-11 interrupt enable register (HCH11INTEN)"]
pub mod hch11inten;
#[doc = "HCH0LEN (rw) register accessor: host channel-0 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch0len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch0len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch0len`]
module"]
#[doc(alias = "HCH0LEN")]
pub type Hch0len = crate::Reg<hch0len::Hch0lenSpec>;
#[doc = "host channel-0 transfer length register"]
pub mod hch0len;
#[doc = "HCH1LEN (rw) register accessor: host channel-1 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch1len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch1len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch1len`]
module"]
#[doc(alias = "HCH1LEN")]
pub type Hch1len = crate::Reg<hch1len::Hch1lenSpec>;
#[doc = "host channel-1 transfer length register"]
pub mod hch1len;
#[doc = "HCH2LEN (rw) register accessor: host channel-2 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch2len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch2len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch2len`]
module"]
#[doc(alias = "HCH2LEN")]
pub type Hch2len = crate::Reg<hch2len::Hch2lenSpec>;
#[doc = "host channel-2 transfer length register"]
pub mod hch2len;
#[doc = "HCH3LEN (rw) register accessor: host channel-3 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch3len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch3len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch3len`]
module"]
#[doc(alias = "HCH3LEN")]
pub type Hch3len = crate::Reg<hch3len::Hch3lenSpec>;
#[doc = "host channel-3 transfer length register"]
pub mod hch3len;
#[doc = "HCH4LEN (rw) register accessor: host channel-4 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch4len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch4len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch4len`]
module"]
#[doc(alias = "HCH4LEN")]
pub type Hch4len = crate::Reg<hch4len::Hch4lenSpec>;
#[doc = "host channel-4 transfer length register"]
pub mod hch4len;
#[doc = "HCH5LEN (rw) register accessor: host channel-5 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch5len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch5len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch5len`]
module"]
#[doc(alias = "HCH5LEN")]
pub type Hch5len = crate::Reg<hch5len::Hch5lenSpec>;
#[doc = "host channel-5 transfer length register"]
pub mod hch5len;
#[doc = "HCH6LEN (rw) register accessor: host channel-6 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch6len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch6len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch6len`]
module"]
#[doc(alias = "HCH6LEN")]
pub type Hch6len = crate::Reg<hch6len::Hch6lenSpec>;
#[doc = "host channel-6 transfer length register"]
pub mod hch6len;
#[doc = "HCH7LEN (rw) register accessor: host channel-7 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch7len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch7len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch7len`]
module"]
#[doc(alias = "HCH7LEN")]
pub type Hch7len = crate::Reg<hch7len::Hch7lenSpec>;
#[doc = "host channel-7 transfer length register"]
pub mod hch7len;
#[doc = "HCH8LEN (rw) register accessor: host channel-8 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch8len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch8len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch8len`]
module"]
#[doc(alias = "HCH8LEN")]
pub type Hch8len = crate::Reg<hch8len::Hch8lenSpec>;
#[doc = "host channel-8 transfer length register"]
pub mod hch8len;
#[doc = "HCH9LEN (rw) register accessor: host channel-9 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch9len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch9len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch9len`]
module"]
#[doc(alias = "HCH9LEN")]
pub type Hch9len = crate::Reg<hch9len::Hch9lenSpec>;
#[doc = "host channel-9 transfer length register"]
pub mod hch9len;
#[doc = "HCH10LEN (rw) register accessor: host channel-10 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch10len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch10len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch10len`]
module"]
#[doc(alias = "HCH10LEN")]
pub type Hch10len = crate::Reg<hch10len::Hch10lenSpec>;
#[doc = "host channel-10 transfer length register"]
pub mod hch10len;
#[doc = "HCH11LEN (rw) register accessor: host channel-11 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch11len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch11len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch11len`]
module"]
#[doc(alias = "HCH11LEN")]
pub type Hch11len = crate::Reg<hch11len::Hch11lenSpec>;
#[doc = "host channel-11 transfer length register"]
pub mod hch11len;
#[doc = "HCH0DMAADDR (rw) register accessor: Host channel 0 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch0dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch0dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch0dmaaddr`]
module"]
#[doc(alias = "HCH0DMAADDR")]
pub type Hch0dmaaddr = crate::Reg<hch0dmaaddr::Hch0dmaaddrSpec>;
#[doc = "Host channel 0 DMA address register"]
pub mod hch0dmaaddr;
#[doc = "HCH1DMAADDR (rw) register accessor: Host channel 1 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch1dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch1dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch1dmaaddr`]
module"]
#[doc(alias = "HCH1DMAADDR")]
pub type Hch1dmaaddr = crate::Reg<hch1dmaaddr::Hch1dmaaddrSpec>;
#[doc = "Host channel 1 DMA address register"]
pub mod hch1dmaaddr;
#[doc = "HCH2DMAADDR (rw) register accessor: Host channel 2 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch2dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch2dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch2dmaaddr`]
module"]
#[doc(alias = "HCH2DMAADDR")]
pub type Hch2dmaaddr = crate::Reg<hch2dmaaddr::Hch2dmaaddrSpec>;
#[doc = "Host channel 2 DMA address register"]
pub mod hch2dmaaddr;
#[doc = "HCH3DMAADDR (rw) register accessor: Host channel 3 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch3dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch3dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch3dmaaddr`]
module"]
#[doc(alias = "HCH3DMAADDR")]
pub type Hch3dmaaddr = crate::Reg<hch3dmaaddr::Hch3dmaaddrSpec>;
#[doc = "Host channel 3 DMA address register"]
pub mod hch3dmaaddr;
#[doc = "HCH4DMAADDR (rw) register accessor: Host channel 4 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch4dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch4dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch4dmaaddr`]
module"]
#[doc(alias = "HCH4DMAADDR")]
pub type Hch4dmaaddr = crate::Reg<hch4dmaaddr::Hch4dmaaddrSpec>;
#[doc = "Host channel 4 DMA address register"]
pub mod hch4dmaaddr;
#[doc = "HCH5DMAADDR (rw) register accessor: Host channel 5 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch5dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch5dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch5dmaaddr`]
module"]
#[doc(alias = "HCH5DMAADDR")]
pub type Hch5dmaaddr = crate::Reg<hch5dmaaddr::Hch5dmaaddrSpec>;
#[doc = "Host channel 5 DMA address register"]
pub mod hch5dmaaddr;
#[doc = "HCH6DMAADDR (rw) register accessor: Host channel 6 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch6dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch6dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch6dmaaddr`]
module"]
#[doc(alias = "HCH6DMAADDR")]
pub type Hch6dmaaddr = crate::Reg<hch6dmaaddr::Hch6dmaaddrSpec>;
#[doc = "Host channel 6 DMA address register"]
pub mod hch6dmaaddr;
#[doc = "HCH7DMAADDR (rw) register accessor: Host channel 7 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch7dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch7dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch7dmaaddr`]
module"]
#[doc(alias = "HCH7DMAADDR")]
pub type Hch7dmaaddr = crate::Reg<hch7dmaaddr::Hch7dmaaddrSpec>;
#[doc = "Host channel 7 DMA address register"]
pub mod hch7dmaaddr;
#[doc = "HCH8DMAADDR (rw) register accessor: Host channel 8 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch8dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch8dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch8dmaaddr`]
module"]
#[doc(alias = "HCH8DMAADDR")]
pub type Hch8dmaaddr = crate::Reg<hch8dmaaddr::Hch8dmaaddrSpec>;
#[doc = "Host channel 8 DMA address register"]
pub mod hch8dmaaddr;
#[doc = "HCH9DMAADDR (rw) register accessor: Host channel 9 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch9dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch9dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch9dmaaddr`]
module"]
#[doc(alias = "HCH9DMAADDR")]
pub type Hch9dmaaddr = crate::Reg<hch9dmaaddr::Hch9dmaaddrSpec>;
#[doc = "Host channel 9 DMA address register"]
pub mod hch9dmaaddr;
#[doc = "HCH10DMAADDR (rw) register accessor: Host channel 10 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch10dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch10dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch10dmaaddr`]
module"]
#[doc(alias = "HCH10DMAADDR")]
pub type Hch10dmaaddr = crate::Reg<hch10dmaaddr::Hch10dmaaddrSpec>;
#[doc = "Host channel 10 DMA address register"]
pub mod hch10dmaaddr;
#[doc = "HCH11DMAADDR (rw) register accessor: Host channel 11 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch11dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch11dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hch11dmaaddr`]
module"]
#[doc(alias = "HCH11DMAADDR")]
pub type Hch11dmaaddr = crate::Reg<hch11dmaaddr::Hch11dmaaddrSpec>;
#[doc = "Host channel 11 DMA address register"]
pub mod hch11dmaaddr;
