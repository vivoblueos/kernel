#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    gotgcs: Gotgcs,
    gotgintf: Gotgintf,
    gahbcs: Gahbcs,
    gusbcs: Gusbcs,
    grstctl: Grstctl,
    gintf: Gintf,
    ginten: Ginten,
    _reserved_7_grstatr: [u8; 0x04],
    _reserved_8_grstatp: [u8; 0x04],
    grflen: Grflen,
    _reserved_10_hnptflen: [u8; 0x04],
    hnptfqstat: Hnptfqstat,
    _reserved12: [u8; 0x08],
    gccfg: Gccfg,
    cid: Cid,
    _reserved14: [u8; 0x14],
    glpmcfg: Glpmcfg,
    pwrd: Pwrd,
    _reserved16: [u8; 0x04],
    adpctl: Adpctl,
    _reserved17: [u8; 0x9c],
    hptflen: Hptflen,
    diep1tflen: Diep1tflen,
    diep2tflen: Diep2tflen,
    diep3tflen: Diep3tflen,
    diep4tflen: Diep4tflen,
    diep5tflen: Diep5tflen,
}
impl RegisterBlock {
    #[doc = "0x00 - Global OTG control and status register (USBFS_GOTGCS)"]
    #[inline(always)]
    pub const fn gotgcs(&self) -> &Gotgcs {
        &self.gotgcs
    }
    #[doc = "0x04 - Global OTG interrupt flag register (USBHS_GOTGINTF)"]
    #[inline(always)]
    pub const fn gotgintf(&self) -> &Gotgintf {
        &self.gotgintf
    }
    #[doc = "0x08 - Global AHB control and status register (USBHS_GAHBCS)"]
    #[inline(always)]
    pub const fn gahbcs(&self) -> &Gahbcs {
        &self.gahbcs
    }
    #[doc = "0x0c - Global USB control and status register (USBHS_GUSBCSR)"]
    #[inline(always)]
    pub const fn gusbcs(&self) -> &Gusbcs {
        &self.gusbcs
    }
    #[doc = "0x10 - Global reset control register (USBHS_GRSTCTL)"]
    #[inline(always)]
    pub const fn grstctl(&self) -> &Grstctl {
        &self.grstctl
    }
    #[doc = "0x14 - Global interrupt flag register (USBFS_GINTF)"]
    #[inline(always)]
    pub const fn gintf(&self) -> &Gintf {
        &self.gintf
    }
    #[doc = "0x18 - Global interrupt enable register (USBHS_GINTEN)"]
    #[inline(always)]
    pub const fn ginten(&self) -> &Ginten {
        &self.ginten
    }
    #[doc = "0x1c - Global Receive status read(Host mode)"]
    #[inline(always)]
    pub const fn grstatr_host(&self) -> &GrstatrHost {
        unsafe { &*(self as *const Self).cast::<u8>().add(28).cast() }
    }
    #[doc = "0x1c - Global Receive status read(Device mode)"]
    #[inline(always)]
    pub const fn grstatr_device(&self) -> &GrstatrDevice {
        unsafe { &*(self as *const Self).cast::<u8>().add(28).cast() }
    }
    #[doc = "0x20 - Global Receive status pop(Host mode)"]
    #[inline(always)]
    pub const fn grstatp_host(&self) -> &GrstatpHost {
        unsafe { &*(self as *const Self).cast::<u8>().add(32).cast() }
    }
    #[doc = "0x20 - Global Receive status pop(Device mode)"]
    #[inline(always)]
    pub const fn grstatp_device(&self) -> &GrstatpDevice {
        unsafe { &*(self as *const Self).cast::<u8>().add(32).cast() }
    }
    #[doc = "0x24 - Global Receive FIFO size register (USBHS_GRFLEN)"]
    #[inline(always)]
    pub const fn grflen(&self) -> &Grflen {
        &self.grflen
    }
    #[doc = "0x28 - Device IN endpoint 0 transmit FIFO length (Device mode)"]
    #[inline(always)]
    pub const fn diep0tflen(&self) -> &Diep0tflen {
        unsafe { &*(self as *const Self).cast::<u8>().add(40).cast() }
    }
    #[doc = "0x28 - Host non-periodic transmit FIFO length register (Host mode)"]
    #[inline(always)]
    pub const fn hnptflen(&self) -> &Hnptflen {
        unsafe { &*(self as *const Self).cast::<u8>().add(40).cast() }
    }
    #[doc = "0x2c - Host non-periodic transmit FIFO/queue status register (HNPTFQSTAT)"]
    #[inline(always)]
    pub const fn hnptfqstat(&self) -> &Hnptfqstat {
        &self.hnptfqstat
    }
    #[doc = "0x38 - Global core configuration register (USBFS_GCCFG)"]
    #[inline(always)]
    pub const fn gccfg(&self) -> &Gccfg {
        &self.gccfg
    }
    #[doc = "0x3c - core ID register"]
    #[inline(always)]
    pub const fn cid(&self) -> &Cid {
        &self.cid
    }
    #[doc = "0x54 - Global core LPM configuration register"]
    #[inline(always)]
    pub const fn glpmcfg(&self) -> &Glpmcfg {
        &self.glpmcfg
    }
    #[doc = "0x58 - Power down register (USBHS_PWRD)"]
    #[inline(always)]
    pub const fn pwrd(&self) -> &Pwrd {
        &self.pwrd
    }
    #[doc = "0x60 - ADP control andstatus register"]
    #[inline(always)]
    pub const fn adpctl(&self) -> &Adpctl {
        &self.adpctl
    }
    #[doc = "0x100 - Host periodic transmit FIFO length register (HPTFLEN)"]
    #[inline(always)]
    pub const fn hptflen(&self) -> &Hptflen {
        &self.hptflen
    }
    #[doc = "0x104 - device IN endpoint transmit FIFO size register"]
    #[inline(always)]
    pub const fn diep1tflen(&self) -> &Diep1tflen {
        &self.diep1tflen
    }
    #[doc = "0x108 - device IN endpoint transmit FIFO size register"]
    #[inline(always)]
    pub const fn diep2tflen(&self) -> &Diep2tflen {
        &self.diep2tflen
    }
    #[doc = "0x10c - device IN endpoint transmit FIFO size register"]
    #[inline(always)]
    pub const fn diep3tflen(&self) -> &Diep3tflen {
        &self.diep3tflen
    }
    #[doc = "0x110 - device IN endpoint transmit FIFO size register"]
    #[inline(always)]
    pub const fn diep4tflen(&self) -> &Diep4tflen {
        &self.diep4tflen
    }
    #[doc = "0x114 - device IN endpoint transmit FIFO size register (FS_DIEP5TXFLEN)"]
    #[inline(always)]
    pub const fn diep5tflen(&self) -> &Diep5tflen {
        &self.diep5tflen
    }
}
#[doc = "GOTGCS (rw) register accessor: Global OTG control and status register (USBFS_GOTGCS)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`gotgcs::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`gotgcs::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gotgcs`]
module"]
#[doc(alias = "GOTGCS")]
pub type Gotgcs = crate::Reg<gotgcs::GotgcsSpec>;
#[doc = "Global OTG control and status register (USBFS_GOTGCS)"]
pub mod gotgcs;
#[doc = "GOTGINTF (rw) register accessor: Global OTG interrupt flag register (USBHS_GOTGINTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`gotgintf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`gotgintf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gotgintf`]
module"]
#[doc(alias = "GOTGINTF")]
pub type Gotgintf = crate::Reg<gotgintf::GotgintfSpec>;
#[doc = "Global OTG interrupt flag register (USBHS_GOTGINTF)"]
pub mod gotgintf;
#[doc = "GAHBCS (rw) register accessor: Global AHB control and status register (USBHS_GAHBCS)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`gahbcs::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`gahbcs::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gahbcs`]
module"]
#[doc(alias = "GAHBCS")]
pub type Gahbcs = crate::Reg<gahbcs::GahbcsSpec>;
#[doc = "Global AHB control and status register (USBHS_GAHBCS)"]
pub mod gahbcs;
#[doc = "GUSBCS (rw) register accessor: Global USB control and status register (USBHS_GUSBCSR)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`gusbcs::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`gusbcs::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gusbcs`]
module"]
#[doc(alias = "GUSBCS")]
pub type Gusbcs = crate::Reg<gusbcs::GusbcsSpec>;
#[doc = "Global USB control and status register (USBHS_GUSBCSR)"]
pub mod gusbcs;
#[doc = "GRSTCTL (rw) register accessor: Global reset control register (USBHS_GRSTCTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`grstctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`grstctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@grstctl`]
module"]
#[doc(alias = "GRSTCTL")]
pub type Grstctl = crate::Reg<grstctl::GrstctlSpec>;
#[doc = "Global reset control register (USBHS_GRSTCTL)"]
pub mod grstctl;
#[doc = "GINTF (rw) register accessor: Global interrupt flag register (USBFS_GINTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`gintf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`gintf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gintf`]
module"]
#[doc(alias = "GINTF")]
pub type Gintf = crate::Reg<gintf::GintfSpec>;
#[doc = "Global interrupt flag register (USBFS_GINTF)"]
pub mod gintf;
#[doc = "GINTEN (rw) register accessor: Global interrupt enable register (USBHS_GINTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ginten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ginten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ginten`]
module"]
#[doc(alias = "GINTEN")]
pub type Ginten = crate::Reg<ginten::GintenSpec>;
#[doc = "Global interrupt enable register (USBHS_GINTEN)"]
pub mod ginten;
#[doc = "GRSTATR_Device (r) register accessor: Global Receive status read(Device mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`grstatr_device::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@grstatr_device`]
module"]
#[doc(alias = "GRSTATR_Device")]
pub type GrstatrDevice = crate::Reg<grstatr_device::GrstatrDeviceSpec>;
#[doc = "Global Receive status read(Device mode)"]
pub mod grstatr_device;
#[doc = "GRSTATR_Host (r) register accessor: Global Receive status read(Host mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`grstatr_host::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@grstatr_host`]
module"]
#[doc(alias = "GRSTATR_Host")]
pub type GrstatrHost = crate::Reg<grstatr_host::GrstatrHostSpec>;
#[doc = "Global Receive status read(Host mode)"]
pub mod grstatr_host;
#[doc = "GRSTATP_Device (r) register accessor: Global Receive status pop(Device mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`grstatp_device::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@grstatp_device`]
module"]
#[doc(alias = "GRSTATP_Device")]
pub type GrstatpDevice = crate::Reg<grstatp_device::GrstatpDeviceSpec>;
#[doc = "Global Receive status pop(Device mode)"]
pub mod grstatp_device;
#[doc = "GRSTATP_Host (r) register accessor: Global Receive status pop(Host mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`grstatp_host::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@grstatp_host`]
module"]
#[doc(alias = "GRSTATP_Host")]
pub type GrstatpHost = crate::Reg<grstatp_host::GrstatpHostSpec>;
#[doc = "Global Receive status pop(Host mode)"]
pub mod grstatp_host;
#[doc = "GRFLEN (rw) register accessor: Global Receive FIFO size register (USBHS_GRFLEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`grflen::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`grflen::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@grflen`]
module"]
#[doc(alias = "GRFLEN")]
pub type Grflen = crate::Reg<grflen::GrflenSpec>;
#[doc = "Global Receive FIFO size register (USBHS_GRFLEN)"]
pub mod grflen;
#[doc = "HNPTFLEN (rw) register accessor: Host non-periodic transmit FIFO length register (Host mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hnptflen::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hnptflen::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hnptflen`]
module"]
#[doc(alias = "HNPTFLEN")]
pub type Hnptflen = crate::Reg<hnptflen::HnptflenSpec>;
#[doc = "Host non-periodic transmit FIFO length register (Host mode)"]
pub mod hnptflen;
#[doc = "DIEP0TFLEN (rw) register accessor: Device IN endpoint 0 transmit FIFO length (Device mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep0tflen::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep0tflen::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep0tflen`]
module"]
#[doc(alias = "DIEP0TFLEN")]
pub type Diep0tflen = crate::Reg<diep0tflen::Diep0tflenSpec>;
#[doc = "Device IN endpoint 0 transmit FIFO length (Device mode)"]
pub mod diep0tflen;
#[doc = "HNPTFQSTAT (r) register accessor: Host non-periodic transmit FIFO/queue status register (HNPTFQSTAT)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hnptfqstat::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hnptfqstat`]
module"]
#[doc(alias = "HNPTFQSTAT")]
pub type Hnptfqstat = crate::Reg<hnptfqstat::HnptfqstatSpec>;
#[doc = "Host non-periodic transmit FIFO/queue status register (HNPTFQSTAT)"]
pub mod hnptfqstat;
#[doc = "GCCFG (rw) register accessor: Global core configuration register (USBFS_GCCFG)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`gccfg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`gccfg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gccfg`]
module"]
#[doc(alias = "GCCFG")]
pub type Gccfg = crate::Reg<gccfg::GccfgSpec>;
#[doc = "Global core configuration register (USBFS_GCCFG)"]
pub mod gccfg;
#[doc = "CID (rw) register accessor: core ID register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cid::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cid::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cid`]
module"]
#[doc(alias = "CID")]
pub type Cid = crate::Reg<cid::CidSpec>;
#[doc = "core ID register"]
pub mod cid;
#[doc = "GLPMCFG (rw) register accessor: Global core LPM configuration register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`glpmcfg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`glpmcfg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@glpmcfg`]
module"]
#[doc(alias = "GLPMCFG")]
pub type Glpmcfg = crate::Reg<glpmcfg::GlpmcfgSpec>;
#[doc = "Global core LPM configuration register"]
pub mod glpmcfg;
#[doc = "PWRD (rw) register accessor: Power down register (USBHS_PWRD)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pwrd::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pwrd::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pwrd`]
module"]
#[doc(alias = "PWRD")]
pub type Pwrd = crate::Reg<pwrd::PwrdSpec>;
#[doc = "Power down register (USBHS_PWRD)"]
pub mod pwrd;
#[doc = "ADPCTL (rw) register accessor: ADP control andstatus register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`adpctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`adpctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@adpctl`]
module"]
#[doc(alias = "ADPCTL")]
pub type Adpctl = crate::Reg<adpctl::AdpctlSpec>;
#[doc = "ADP control andstatus register"]
pub mod adpctl;
#[doc = "HPTFLEN (rw) register accessor: Host periodic transmit FIFO length register (HPTFLEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hptflen::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hptflen::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hptflen`]
module"]
#[doc(alias = "HPTFLEN")]
pub type Hptflen = crate::Reg<hptflen::HptflenSpec>;
#[doc = "Host periodic transmit FIFO length register (HPTFLEN)"]
pub mod hptflen;
#[doc = "DIEP1TFLEN (rw) register accessor: device IN endpoint transmit FIFO size register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep1tflen::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep1tflen::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep1tflen`]
module"]
#[doc(alias = "DIEP1TFLEN")]
pub type Diep1tflen = crate::Reg<diep1tflen::Diep1tflenSpec>;
#[doc = "device IN endpoint transmit FIFO size register"]
pub mod diep1tflen;
#[doc = "DIEP2TFLEN (rw) register accessor: device IN endpoint transmit FIFO size register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep2tflen::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep2tflen::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep2tflen`]
module"]
#[doc(alias = "DIEP2TFLEN")]
pub type Diep2tflen = crate::Reg<diep2tflen::Diep2tflenSpec>;
#[doc = "device IN endpoint transmit FIFO size register"]
pub mod diep2tflen;
#[doc = "DIEP3TFLEN (rw) register accessor: device IN endpoint transmit FIFO size register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep3tflen::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep3tflen::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep3tflen`]
module"]
#[doc(alias = "DIEP3TFLEN")]
pub type Diep3tflen = crate::Reg<diep3tflen::Diep3tflenSpec>;
#[doc = "device IN endpoint transmit FIFO size register"]
pub mod diep3tflen;
#[doc = "DIEP4TFLEN (rw) register accessor: device IN endpoint transmit FIFO size register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep4tflen::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep4tflen::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep4tflen`]
module"]
#[doc(alias = "DIEP4TFLEN")]
pub type Diep4tflen = crate::Reg<diep4tflen::Diep4tflenSpec>;
#[doc = "device IN endpoint transmit FIFO size register"]
pub mod diep4tflen;
#[doc = "DIEP5TFLEN (rw) register accessor: device IN endpoint transmit FIFO size register (FS_DIEP5TXFLEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep5tflen::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep5tflen::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep5tflen`]
module"]
#[doc(alias = "DIEP5TFLEN")]
pub type Diep5tflen = crate::Reg<diep5tflen::Diep5tflenSpec>;
#[doc = "device IN endpoint transmit FIFO size register (FS_DIEP5TXFLEN)"]
pub mod diep5tflen;
