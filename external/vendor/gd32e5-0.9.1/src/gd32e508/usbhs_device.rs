#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    dcfg: Dcfg,
    dctl: Dctl,
    dstat: Dstat,
    _reserved3: [u8; 0x04],
    diepinten: Diepinten,
    doepinten: Doepinten,
    daepint: Daepint,
    daepinten: Daepinten,
    _reserved7: [u8; 0x08],
    dvbusdt: Dvbusdt,
    dvbuspt: Dvbuspt,
    _reserved9: [u8; 0x04],
    diepfeinten: Diepfeinten,
    dep1int: Dep1int,
    dep1inten: Dep1inten,
    _reserved12: [u8; 0x04],
    diep1inten: Diep1inten,
    _reserved13: [u8; 0x3c],
    doep1inten: Doep1inten,
    _reserved14: [u8; 0x78],
    diep0ctl: Diep0ctl,
    _reserved15: [u8; 0x04],
    diep0intf: Diep0intf,
    _reserved16: [u8; 0x04],
    diep0len: Diep0len,
    diep0dmaaddr: Diep0dmaaddr,
    diep0tfstat: Diep0tfstat,
    _reserved19: [u8; 0x04],
    diep1ctl: Diep1ctl,
    _reserved20: [u8; 0x04],
    diep1intf: Diep1intf,
    _reserved21: [u8; 0x04],
    diep1len: Diep1len,
    diep1dmaaddr: Diep1dmaaddr,
    diep1tfstat: Diep1tfstat,
    _reserved24: [u8; 0x04],
    diep2ctl: Diep2ctl,
    _reserved25: [u8; 0x04],
    diep2intf: Diep2intf,
    _reserved26: [u8; 0x04],
    diep2len: Diep2len,
    diep2dmaaddr: Diep2dmaaddr,
    diep2tfstat: Diep2tfstat,
    _reserved29: [u8; 0x04],
    diep3ctl: Diep3ctl,
    _reserved30: [u8; 0x04],
    diep3intf: Diep3intf,
    _reserved31: [u8; 0x04],
    diep3len: Diep3len,
    diep3dmaaddr: Diep3dmaaddr,
    diep3tfstat: Diep3tfstat,
    _reserved34: [u8; 0x04],
    diep4ctl: Diep4ctl,
    _reserved35: [u8; 0x04],
    diep4intf: Diep4intf,
    _reserved36: [u8; 0x04],
    diep4len: Diep4len,
    diep4dmaaddr: Diep4dmaaddr,
    diep4tfstat: Diep4tfstat,
    _reserved39: [u8; 0x04],
    diep5ctl: Diep5ctl,
    _reserved40: [u8; 0x04],
    diep5intf: Diep5intf,
    _reserved41: [u8; 0x04],
    diep5len: Diep5len,
    diep5dmaaddr: Diep5dmaaddr,
    diep5tfstat: Diep5tfstat,
    _reserved44: [u8; 0x0144],
    doep0ctl: Doep0ctl,
    _reserved45: [u8; 0x04],
    doep0intf: Doep0intf,
    _reserved46: [u8; 0x04],
    doep0len: Doep0len,
    doep0dmaaddr: Doep0dmaaddr,
    _reserved48: [u8; 0x08],
    doep1ctl: Doep1ctl,
    _reserved49: [u8; 0x04],
    doep1intf: Doep1intf,
    _reserved50: [u8; 0x04],
    doep1len: Doep1len,
    doep1dmaaddr: Doep1dmaaddr,
    _reserved52: [u8; 0x08],
    doep2ctl: Doep2ctl,
    _reserved53: [u8; 0x04],
    doep2intf: Doep2intf,
    _reserved54: [u8; 0x04],
    doep2len: Doep2len,
    doep2dmaaddr: Doep2dmaaddr,
    _reserved56: [u8; 0x08],
    doep3ctl: Doep3ctl,
    _reserved57: [u8; 0x04],
    doep3intf: Doep3intf,
    _reserved58: [u8; 0x04],
    doep3len: Doep3len,
    doep3dmaaddr: Doep3dmaaddr,
    _reserved60: [u8; 0x08],
    doep4ctl: Doep4ctl,
    _reserved61: [u8; 0x04],
    doep4intf: Doep4intf,
    _reserved62: [u8; 0x04],
    doep4len: Doep4len,
    doep4dmaaddr: Doep4dmaaddr,
    _reserved64: [u8; 0x08],
    doep5ctl: Doep5ctl,
    _reserved65: [u8; 0x04],
    doep5intf: Doep5intf,
    _reserved66: [u8; 0x04],
    doep5len: Doep5len,
    doep5dmaaddr: Doep5dmaaddr,
}
impl RegisterBlock {
    #[doc = "0x00 - device configuration register (DCFG)"]
    #[inline(always)]
    pub const fn dcfg(&self) -> &Dcfg {
        &self.dcfg
    }
    #[doc = "0x04 - device control register (DCTL)"]
    #[inline(always)]
    pub const fn dctl(&self) -> &Dctl {
        &self.dctl
    }
    #[doc = "0x08 - device status register (DSTAT)"]
    #[inline(always)]
    pub const fn dstat(&self) -> &Dstat {
        &self.dstat
    }
    #[doc = "0x10 - device IN endpoint common interrupt mask register (DIEPINTEN)"]
    #[inline(always)]
    pub const fn diepinten(&self) -> &Diepinten {
        &self.diepinten
    }
    #[doc = "0x14 - device OUT endpoint common interrupt enable register (DOEPINTEN)"]
    #[inline(always)]
    pub const fn doepinten(&self) -> &Doepinten {
        &self.doepinten
    }
    #[doc = "0x18 - device all endpoints interrupt register (DAEPINT)"]
    #[inline(always)]
    pub const fn daepint(&self) -> &Daepint {
        &self.daepint
    }
    #[doc = "0x1c - Device all endpoints interrupt enable register (DAEPINTEN)"]
    #[inline(always)]
    pub const fn daepinten(&self) -> &Daepinten {
        &self.daepinten
    }
    #[doc = "0x28 - device VBUS discharge time register"]
    #[inline(always)]
    pub const fn dvbusdt(&self) -> &Dvbusdt {
        &self.dvbusdt
    }
    #[doc = "0x2c - device VBUS pulsing time register"]
    #[inline(always)]
    pub const fn dvbuspt(&self) -> &Dvbuspt {
        &self.dvbuspt
    }
    #[doc = "0x34 - device IN endpoint FIFO empty interrupt enable register"]
    #[inline(always)]
    pub const fn diepfeinten(&self) -> &Diepfeinten {
        &self.diepfeinten
    }
    #[doc = "0x38 - Device endpoint 1 interrupt register"]
    #[inline(always)]
    pub const fn dep1int(&self) -> &Dep1int {
        &self.dep1int
    }
    #[doc = "0x3c - Device endpoint 1 interrupt register"]
    #[inline(always)]
    pub const fn dep1inten(&self) -> &Dep1inten {
        &self.dep1inten
    }
    #[doc = "0x44 - Device IN endpoint 1 interrupt enable register"]
    #[inline(always)]
    pub const fn diep1inten(&self) -> &Diep1inten {
        &self.diep1inten
    }
    #[doc = "0x84 - Device OUT endpoint 1 interrupt enable register"]
    #[inline(always)]
    pub const fn doep1inten(&self) -> &Doep1inten {
        &self.doep1inten
    }
    #[doc = "0x100 - device IN endpoint 0 control register (DIEP0CTL)"]
    #[inline(always)]
    pub const fn diep0ctl(&self) -> &Diep0ctl {
        &self.diep0ctl
    }
    #[doc = "0x108 - device endpoint-0 interrupt register"]
    #[inline(always)]
    pub const fn diep0intf(&self) -> &Diep0intf {
        &self.diep0intf
    }
    #[doc = "0x110 - device IN endpoint-0 transfer length register"]
    #[inline(always)]
    pub const fn diep0len(&self) -> &Diep0len {
        &self.diep0len
    }
    #[doc = "0x114 - Device IN endpoint 0 DMA address register"]
    #[inline(always)]
    pub const fn diep0dmaaddr(&self) -> &Diep0dmaaddr {
        &self.diep0dmaaddr
    }
    #[doc = "0x118 - device IN endpoint 0 transmit FIFO status register"]
    #[inline(always)]
    pub const fn diep0tfstat(&self) -> &Diep0tfstat {
        &self.diep0tfstat
    }
    #[doc = "0x120 - device in endpoint-1 control register"]
    #[inline(always)]
    pub const fn diep1ctl(&self) -> &Diep1ctl {
        &self.diep1ctl
    }
    #[doc = "0x128 - device endpoint-1 interrupt register"]
    #[inline(always)]
    pub const fn diep1intf(&self) -> &Diep1intf {
        &self.diep1intf
    }
    #[doc = "0x130 - device IN endpoint-1 transfer length register"]
    #[inline(always)]
    pub const fn diep1len(&self) -> &Diep1len {
        &self.diep1len
    }
    #[doc = "0x134 - Device IN endpoint 1 DMA address register"]
    #[inline(always)]
    pub const fn diep1dmaaddr(&self) -> &Diep1dmaaddr {
        &self.diep1dmaaddr
    }
    #[doc = "0x138 - device IN endpoint 1 transmit FIFO status register"]
    #[inline(always)]
    pub const fn diep1tfstat(&self) -> &Diep1tfstat {
        &self.diep1tfstat
    }
    #[doc = "0x140 - device endpoint-2 control register"]
    #[inline(always)]
    pub const fn diep2ctl(&self) -> &Diep2ctl {
        &self.diep2ctl
    }
    #[doc = "0x148 - device endpoint-2 interrupt register"]
    #[inline(always)]
    pub const fn diep2intf(&self) -> &Diep2intf {
        &self.diep2intf
    }
    #[doc = "0x150 - device IN endpoint-2 transfer length register"]
    #[inline(always)]
    pub const fn diep2len(&self) -> &Diep2len {
        &self.diep2len
    }
    #[doc = "0x154 - Device IN endpoint 2 DMA address register"]
    #[inline(always)]
    pub const fn diep2dmaaddr(&self) -> &Diep2dmaaddr {
        &self.diep2dmaaddr
    }
    #[doc = "0x158 - device IN endpoint 2 transmit FIFO status register"]
    #[inline(always)]
    pub const fn diep2tfstat(&self) -> &Diep2tfstat {
        &self.diep2tfstat
    }
    #[doc = "0x160 - device endpoint-3 control register"]
    #[inline(always)]
    pub const fn diep3ctl(&self) -> &Diep3ctl {
        &self.diep3ctl
    }
    #[doc = "0x168 - device endpoint-3 interrupt register"]
    #[inline(always)]
    pub const fn diep3intf(&self) -> &Diep3intf {
        &self.diep3intf
    }
    #[doc = "0x170 - device IN endpoint-3 transfer length register"]
    #[inline(always)]
    pub const fn diep3len(&self) -> &Diep3len {
        &self.diep3len
    }
    #[doc = "0x174 - Device IN endpoint 3 DMA address register"]
    #[inline(always)]
    pub const fn diep3dmaaddr(&self) -> &Diep3dmaaddr {
        &self.diep3dmaaddr
    }
    #[doc = "0x178 - device IN endpoint 3 transmit FIFO status register"]
    #[inline(always)]
    pub const fn diep3tfstat(&self) -> &Diep3tfstat {
        &self.diep3tfstat
    }
    #[doc = "0x180 - device endpoint-4 control register"]
    #[inline(always)]
    pub const fn diep4ctl(&self) -> &Diep4ctl {
        &self.diep4ctl
    }
    #[doc = "0x188 - device endpoint-4 interrupt register"]
    #[inline(always)]
    pub const fn diep4intf(&self) -> &Diep4intf {
        &self.diep4intf
    }
    #[doc = "0x190 - device IN endpoint-4 transfer length register"]
    #[inline(always)]
    pub const fn diep4len(&self) -> &Diep4len {
        &self.diep4len
    }
    #[doc = "0x194 - Device IN endpoint 4 DMA address register"]
    #[inline(always)]
    pub const fn diep4dmaaddr(&self) -> &Diep4dmaaddr {
        &self.diep4dmaaddr
    }
    #[doc = "0x198 - device IN endpoint 4 transmit FIFO status register"]
    #[inline(always)]
    pub const fn diep4tfstat(&self) -> &Diep4tfstat {
        &self.diep4tfstat
    }
    #[doc = "0x1a0 - device endpoint-5 control register"]
    #[inline(always)]
    pub const fn diep5ctl(&self) -> &Diep5ctl {
        &self.diep5ctl
    }
    #[doc = "0x1a8 - device endpoint-5 interrupt register"]
    #[inline(always)]
    pub const fn diep5intf(&self) -> &Diep5intf {
        &self.diep5intf
    }
    #[doc = "0x1b0 - device IN endpoint-5 transfer length register"]
    #[inline(always)]
    pub const fn diep5len(&self) -> &Diep5len {
        &self.diep5len
    }
    #[doc = "0x1b4 - Device IN endpoint 5 DMA address register"]
    #[inline(always)]
    pub const fn diep5dmaaddr(&self) -> &Diep5dmaaddr {
        &self.diep5dmaaddr
    }
    #[doc = "0x1b8 - device IN endpoint 5 transmit FIFO status register"]
    #[inline(always)]
    pub const fn diep5tfstat(&self) -> &Diep5tfstat {
        &self.diep5tfstat
    }
    #[doc = "0x300 - device endpoint-0 control register"]
    #[inline(always)]
    pub const fn doep0ctl(&self) -> &Doep0ctl {
        &self.doep0ctl
    }
    #[doc = "0x308 - device out endpoint-0 interrupt flag register"]
    #[inline(always)]
    pub const fn doep0intf(&self) -> &Doep0intf {
        &self.doep0intf
    }
    #[doc = "0x310 - device OUT endpoint-0 transfer length register"]
    #[inline(always)]
    pub const fn doep0len(&self) -> &Doep0len {
        &self.doep0len
    }
    #[doc = "0x314 - Device OUT endpoint 0 DMA address register"]
    #[inline(always)]
    pub const fn doep0dmaaddr(&self) -> &Doep0dmaaddr {
        &self.doep0dmaaddr
    }
    #[doc = "0x320 - device endpoint-1 control register"]
    #[inline(always)]
    pub const fn doep1ctl(&self) -> &Doep1ctl {
        &self.doep1ctl
    }
    #[doc = "0x328 - device out endpoint-1 interrupt flag register"]
    #[inline(always)]
    pub const fn doep1intf(&self) -> &Doep1intf {
        &self.doep1intf
    }
    #[doc = "0x330 - device OUT endpoint-1 transfer length register"]
    #[inline(always)]
    pub const fn doep1len(&self) -> &Doep1len {
        &self.doep1len
    }
    #[doc = "0x334 - Device OUT endpoint 1 DMA address register"]
    #[inline(always)]
    pub const fn doep1dmaaddr(&self) -> &Doep1dmaaddr {
        &self.doep1dmaaddr
    }
    #[doc = "0x340 - device endpoint-2 control register"]
    #[inline(always)]
    pub const fn doep2ctl(&self) -> &Doep2ctl {
        &self.doep2ctl
    }
    #[doc = "0x348 - device out endpoint-2 interrupt flag register"]
    #[inline(always)]
    pub const fn doep2intf(&self) -> &Doep2intf {
        &self.doep2intf
    }
    #[doc = "0x350 - device OUT endpoint-2 transfer length register"]
    #[inline(always)]
    pub const fn doep2len(&self) -> &Doep2len {
        &self.doep2len
    }
    #[doc = "0x354 - Device OUT endpoint 2 DMA address register"]
    #[inline(always)]
    pub const fn doep2dmaaddr(&self) -> &Doep2dmaaddr {
        &self.doep2dmaaddr
    }
    #[doc = "0x360 - device endpoint-3 control register"]
    #[inline(always)]
    pub const fn doep3ctl(&self) -> &Doep3ctl {
        &self.doep3ctl
    }
    #[doc = "0x368 - device out endpoint-3 interrupt flag register"]
    #[inline(always)]
    pub const fn doep3intf(&self) -> &Doep3intf {
        &self.doep3intf
    }
    #[doc = "0x370 - device OUT endpoint-3 transfer length register"]
    #[inline(always)]
    pub const fn doep3len(&self) -> &Doep3len {
        &self.doep3len
    }
    #[doc = "0x374 - Device OUT endpoint 3 DMA address register"]
    #[inline(always)]
    pub const fn doep3dmaaddr(&self) -> &Doep3dmaaddr {
        &self.doep3dmaaddr
    }
    #[doc = "0x380 - device endpoint-4 control register"]
    #[inline(always)]
    pub const fn doep4ctl(&self) -> &Doep4ctl {
        &self.doep4ctl
    }
    #[doc = "0x388 - device out endpoint-4 interrupt flag register"]
    #[inline(always)]
    pub const fn doep4intf(&self) -> &Doep4intf {
        &self.doep4intf
    }
    #[doc = "0x390 - device OUT endpoint-4 transfer length register"]
    #[inline(always)]
    pub const fn doep4len(&self) -> &Doep4len {
        &self.doep4len
    }
    #[doc = "0x394 - Device OUT endpoint 4 DMA address register"]
    #[inline(always)]
    pub const fn doep4dmaaddr(&self) -> &Doep4dmaaddr {
        &self.doep4dmaaddr
    }
    #[doc = "0x3a0 - device endpoint-5 control register"]
    #[inline(always)]
    pub const fn doep5ctl(&self) -> &Doep5ctl {
        &self.doep5ctl
    }
    #[doc = "0x3a8 - device out endpoint-5 interrupt flag register"]
    #[inline(always)]
    pub const fn doep5intf(&self) -> &Doep5intf {
        &self.doep5intf
    }
    #[doc = "0x3b0 - device OUT endpoint-5 transfer length register"]
    #[inline(always)]
    pub const fn doep5len(&self) -> &Doep5len {
        &self.doep5len
    }
    #[doc = "0x3b4 - Device OUT endpoint 5 DMA address register"]
    #[inline(always)]
    pub const fn doep5dmaaddr(&self) -> &Doep5dmaaddr {
        &self.doep5dmaaddr
    }
}
#[doc = "DCFG (rw) register accessor: device configuration register (DCFG)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dcfg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dcfg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dcfg`]
module"]
#[doc(alias = "DCFG")]
pub type Dcfg = crate::Reg<dcfg::DcfgSpec>;
#[doc = "device configuration register (DCFG)"]
pub mod dcfg;
#[doc = "DCTL (rw) register accessor: device control register (DCTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dctl`]
module"]
#[doc(alias = "DCTL")]
pub type Dctl = crate::Reg<dctl::DctlSpec>;
#[doc = "device control register (DCTL)"]
pub mod dctl;
#[doc = "DSTAT (r) register accessor: device status register (DSTAT)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dstat::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dstat`]
module"]
#[doc(alias = "DSTAT")]
pub type Dstat = crate::Reg<dstat::DstatSpec>;
#[doc = "device status register (DSTAT)"]
pub mod dstat;
#[doc = "DIEPINTEN (rw) register accessor: device IN endpoint common interrupt mask register (DIEPINTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diepinten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diepinten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diepinten`]
module"]
#[doc(alias = "DIEPINTEN")]
pub type Diepinten = crate::Reg<diepinten::DiepintenSpec>;
#[doc = "device IN endpoint common interrupt mask register (DIEPINTEN)"]
pub mod diepinten;
#[doc = "DOEPINTEN (rw) register accessor: device OUT endpoint common interrupt enable register (DOEPINTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doepinten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doepinten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doepinten`]
module"]
#[doc(alias = "DOEPINTEN")]
pub type Doepinten = crate::Reg<doepinten::DoepintenSpec>;
#[doc = "device OUT endpoint common interrupt enable register (DOEPINTEN)"]
pub mod doepinten;
#[doc = "DAEPINT (r) register accessor: device all endpoints interrupt register (DAEPINT)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`daepint::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@daepint`]
module"]
#[doc(alias = "DAEPINT")]
pub type Daepint = crate::Reg<daepint::DaepintSpec>;
#[doc = "device all endpoints interrupt register (DAEPINT)"]
pub mod daepint;
#[doc = "DAEPINTEN (rw) register accessor: Device all endpoints interrupt enable register (DAEPINTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`daepinten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`daepinten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@daepinten`]
module"]
#[doc(alias = "DAEPINTEN")]
pub type Daepinten = crate::Reg<daepinten::DaepintenSpec>;
#[doc = "Device all endpoints interrupt enable register (DAEPINTEN)"]
pub mod daepinten;
#[doc = "DVBUSDT (rw) register accessor: device VBUS discharge time register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dvbusdt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dvbusdt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dvbusdt`]
module"]
#[doc(alias = "DVBUSDT")]
pub type Dvbusdt = crate::Reg<dvbusdt::DvbusdtSpec>;
#[doc = "device VBUS discharge time register"]
pub mod dvbusdt;
#[doc = "DVBUSPT (rw) register accessor: device VBUS pulsing time register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dvbuspt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dvbuspt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dvbuspt`]
module"]
#[doc(alias = "DVBUSPT")]
pub type Dvbuspt = crate::Reg<dvbuspt::DvbusptSpec>;
#[doc = "device VBUS pulsing time register"]
pub mod dvbuspt;
#[doc = "DIEPFEINTEN (rw) register accessor: device IN endpoint FIFO empty interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diepfeinten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diepfeinten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diepfeinten`]
module"]
#[doc(alias = "DIEPFEINTEN")]
pub type Diepfeinten = crate::Reg<diepfeinten::DiepfeintenSpec>;
#[doc = "device IN endpoint FIFO empty interrupt enable register"]
pub mod diepfeinten;
#[doc = "DEP1INT (r) register accessor: Device endpoint 1 interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dep1int::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dep1int`]
module"]
#[doc(alias = "DEP1INT")]
pub type Dep1int = crate::Reg<dep1int::Dep1intSpec>;
#[doc = "Device endpoint 1 interrupt register"]
pub mod dep1int;
#[doc = "DEP1INTEN (r) register accessor: Device endpoint 1 interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dep1inten::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dep1inten`]
module"]
#[doc(alias = "DEP1INTEN")]
pub type Dep1inten = crate::Reg<dep1inten::Dep1intenSpec>;
#[doc = "Device endpoint 1 interrupt register"]
pub mod dep1inten;
#[doc = "DIEP1INTEN (rw) register accessor: Device IN endpoint 1 interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep1inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep1inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep1inten`]
module"]
#[doc(alias = "DIEP1INTEN")]
pub type Diep1inten = crate::Reg<diep1inten::Diep1intenSpec>;
#[doc = "Device IN endpoint 1 interrupt enable register"]
pub mod diep1inten;
#[doc = "DOEP1INTEN (rw) register accessor: Device OUT endpoint 1 interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep1inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep1inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep1inten`]
module"]
#[doc(alias = "DOEP1INTEN")]
pub type Doep1inten = crate::Reg<doep1inten::Doep1intenSpec>;
#[doc = "Device OUT endpoint 1 interrupt enable register"]
pub mod doep1inten;
#[doc = "DIEP0CTL (rw) register accessor: device IN endpoint 0 control register (DIEP0CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep0ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep0ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep0ctl`]
module"]
#[doc(alias = "DIEP0CTL")]
pub type Diep0ctl = crate::Reg<diep0ctl::Diep0ctlSpec>;
#[doc = "device IN endpoint 0 control register (DIEP0CTL)"]
pub mod diep0ctl;
#[doc = "DIEP1CTL (rw) register accessor: device in endpoint-1 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep1ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep1ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep1ctl`]
module"]
#[doc(alias = "DIEP1CTL")]
pub type Diep1ctl = crate::Reg<diep1ctl::Diep1ctlSpec>;
#[doc = "device in endpoint-1 control register"]
pub mod diep1ctl;
#[doc = "DIEP2CTL (rw) register accessor: device endpoint-2 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep2ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep2ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep2ctl`]
module"]
#[doc(alias = "DIEP2CTL")]
pub type Diep2ctl = crate::Reg<diep2ctl::Diep2ctlSpec>;
#[doc = "device endpoint-2 control register"]
pub mod diep2ctl;
#[doc = "DIEP3CTL (rw) register accessor: device endpoint-3 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep3ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep3ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep3ctl`]
module"]
#[doc(alias = "DIEP3CTL")]
pub type Diep3ctl = crate::Reg<diep3ctl::Diep3ctlSpec>;
#[doc = "device endpoint-3 control register"]
pub mod diep3ctl;
#[doc = "DIEP4CTL (rw) register accessor: device endpoint-4 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep4ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep4ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep4ctl`]
module"]
#[doc(alias = "DIEP4CTL")]
pub type Diep4ctl = crate::Reg<diep4ctl::Diep4ctlSpec>;
#[doc = "device endpoint-4 control register"]
pub mod diep4ctl;
#[doc = "DIEP5CTL (rw) register accessor: device endpoint-5 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep5ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep5ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep5ctl`]
module"]
#[doc(alias = "DIEP5CTL")]
pub type Diep5ctl = crate::Reg<diep5ctl::Diep5ctlSpec>;
#[doc = "device endpoint-5 control register"]
pub mod diep5ctl;
#[doc = "DOEP0CTL (rw) register accessor: device endpoint-0 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep0ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep0ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep0ctl`]
module"]
#[doc(alias = "DOEP0CTL")]
pub type Doep0ctl = crate::Reg<doep0ctl::Doep0ctlSpec>;
#[doc = "device endpoint-0 control register"]
pub mod doep0ctl;
#[doc = "DOEP1CTL (rw) register accessor: device endpoint-1 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep1ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep1ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep1ctl`]
module"]
#[doc(alias = "DOEP1CTL")]
pub type Doep1ctl = crate::Reg<doep1ctl::Doep1ctlSpec>;
#[doc = "device endpoint-1 control register"]
pub mod doep1ctl;
#[doc = "DOEP2CTL (rw) register accessor: device endpoint-2 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep2ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep2ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep2ctl`]
module"]
#[doc(alias = "DOEP2CTL")]
pub type Doep2ctl = crate::Reg<doep2ctl::Doep2ctlSpec>;
#[doc = "device endpoint-2 control register"]
pub mod doep2ctl;
#[doc = "DOEP3CTL (rw) register accessor: device endpoint-3 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep3ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep3ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep3ctl`]
module"]
#[doc(alias = "DOEP3CTL")]
pub type Doep3ctl = crate::Reg<doep3ctl::Doep3ctlSpec>;
#[doc = "device endpoint-3 control register"]
pub mod doep3ctl;
#[doc = "DOEP4CTL (rw) register accessor: device endpoint-4 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep4ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep4ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep4ctl`]
module"]
#[doc(alias = "DOEP4CTL")]
pub type Doep4ctl = crate::Reg<doep4ctl::Doep4ctlSpec>;
#[doc = "device endpoint-4 control register"]
pub mod doep4ctl;
#[doc = "DOEP5CTL (rw) register accessor: device endpoint-5 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep5ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep5ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep5ctl`]
module"]
#[doc(alias = "DOEP5CTL")]
pub type Doep5ctl = crate::Reg<doep5ctl::Doep5ctlSpec>;
#[doc = "device endpoint-5 control register"]
pub mod doep5ctl;
#[doc = "DIEP0INTF (rw) register accessor: device endpoint-0 interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep0intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep0intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep0intf`]
module"]
#[doc(alias = "DIEP0INTF")]
pub type Diep0intf = crate::Reg<diep0intf::Diep0intfSpec>;
#[doc = "device endpoint-0 interrupt register"]
pub mod diep0intf;
#[doc = "DIEP1INTF (rw) register accessor: device endpoint-1 interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep1intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep1intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep1intf`]
module"]
#[doc(alias = "DIEP1INTF")]
pub type Diep1intf = crate::Reg<diep1intf::Diep1intfSpec>;
#[doc = "device endpoint-1 interrupt register"]
pub mod diep1intf;
#[doc = "DIEP2INTF (rw) register accessor: device endpoint-2 interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep2intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep2intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep2intf`]
module"]
#[doc(alias = "DIEP2INTF")]
pub type Diep2intf = crate::Reg<diep2intf::Diep2intfSpec>;
#[doc = "device endpoint-2 interrupt register"]
pub mod diep2intf;
#[doc = "DIEP3INTF (rw) register accessor: device endpoint-3 interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep3intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep3intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep3intf`]
module"]
#[doc(alias = "DIEP3INTF")]
pub type Diep3intf = crate::Reg<diep3intf::Diep3intfSpec>;
#[doc = "device endpoint-3 interrupt register"]
pub mod diep3intf;
#[doc = "DIEP4INTF (rw) register accessor: device endpoint-4 interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep4intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep4intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep4intf`]
module"]
#[doc(alias = "DIEP4INTF")]
pub type Diep4intf = crate::Reg<diep4intf::Diep4intfSpec>;
#[doc = "device endpoint-4 interrupt register"]
pub mod diep4intf;
#[doc = "DIEP5INTF (rw) register accessor: device endpoint-5 interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep5intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep5intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep5intf`]
module"]
#[doc(alias = "DIEP5INTF")]
pub type Diep5intf = crate::Reg<diep5intf::Diep5intfSpec>;
#[doc = "device endpoint-5 interrupt register"]
pub mod diep5intf;
#[doc = "DOEP0INTF (rw) register accessor: device out endpoint-0 interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep0intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep0intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep0intf`]
module"]
#[doc(alias = "DOEP0INTF")]
pub type Doep0intf = crate::Reg<doep0intf::Doep0intfSpec>;
#[doc = "device out endpoint-0 interrupt flag register"]
pub mod doep0intf;
#[doc = "DOEP1INTF (rw) register accessor: device out endpoint-1 interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep1intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep1intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep1intf`]
module"]
#[doc(alias = "DOEP1INTF")]
pub type Doep1intf = crate::Reg<doep1intf::Doep1intfSpec>;
#[doc = "device out endpoint-1 interrupt flag register"]
pub mod doep1intf;
#[doc = "DOEP2INTF (rw) register accessor: device out endpoint-2 interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep2intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep2intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep2intf`]
module"]
#[doc(alias = "DOEP2INTF")]
pub type Doep2intf = crate::Reg<doep2intf::Doep2intfSpec>;
#[doc = "device out endpoint-2 interrupt flag register"]
pub mod doep2intf;
#[doc = "DOEP3INTF (rw) register accessor: device out endpoint-3 interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep3intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep3intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep3intf`]
module"]
#[doc(alias = "DOEP3INTF")]
pub type Doep3intf = crate::Reg<doep3intf::Doep3intfSpec>;
#[doc = "device out endpoint-3 interrupt flag register"]
pub mod doep3intf;
#[doc = "DOEP4INTF (rw) register accessor: device out endpoint-4 interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep4intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep4intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep4intf`]
module"]
#[doc(alias = "DOEP4INTF")]
pub type Doep4intf = crate::Reg<doep4intf::Doep4intfSpec>;
#[doc = "device out endpoint-4 interrupt flag register"]
pub mod doep4intf;
#[doc = "DOEP5INTF (rw) register accessor: device out endpoint-5 interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep5intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep5intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep5intf`]
module"]
#[doc(alias = "DOEP5INTF")]
pub type Doep5intf = crate::Reg<doep5intf::Doep5intfSpec>;
#[doc = "device out endpoint-5 interrupt flag register"]
pub mod doep5intf;
#[doc = "DIEP0LEN (rw) register accessor: device IN endpoint-0 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep0len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep0len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep0len`]
module"]
#[doc(alias = "DIEP0LEN")]
pub type Diep0len = crate::Reg<diep0len::Diep0lenSpec>;
#[doc = "device IN endpoint-0 transfer length register"]
pub mod diep0len;
#[doc = "DOEP0LEN (rw) register accessor: device OUT endpoint-0 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep0len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep0len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep0len`]
module"]
#[doc(alias = "DOEP0LEN")]
pub type Doep0len = crate::Reg<doep0len::Doep0lenSpec>;
#[doc = "device OUT endpoint-0 transfer length register"]
pub mod doep0len;
#[doc = "DIEP1LEN (rw) register accessor: device IN endpoint-1 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep1len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep1len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep1len`]
module"]
#[doc(alias = "DIEP1LEN")]
pub type Diep1len = crate::Reg<diep1len::Diep1lenSpec>;
#[doc = "device IN endpoint-1 transfer length register"]
pub mod diep1len;
#[doc = "DIEP2LEN (rw) register accessor: device IN endpoint-2 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep2len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep2len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep2len`]
module"]
#[doc(alias = "DIEP2LEN")]
pub type Diep2len = crate::Reg<diep2len::Diep2lenSpec>;
#[doc = "device IN endpoint-2 transfer length register"]
pub mod diep2len;
#[doc = "DIEP3LEN (rw) register accessor: device IN endpoint-3 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep3len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep3len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep3len`]
module"]
#[doc(alias = "DIEP3LEN")]
pub type Diep3len = crate::Reg<diep3len::Diep3lenSpec>;
#[doc = "device IN endpoint-3 transfer length register"]
pub mod diep3len;
#[doc = "DIEP4LEN (rw) register accessor: device IN endpoint-4 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep4len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep4len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep4len`]
module"]
#[doc(alias = "DIEP4LEN")]
pub type Diep4len = crate::Reg<diep4len::Diep4lenSpec>;
#[doc = "device IN endpoint-4 transfer length register"]
pub mod diep4len;
#[doc = "DIEP5LEN (rw) register accessor: device IN endpoint-5 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep5len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep5len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep5len`]
module"]
#[doc(alias = "DIEP5LEN")]
pub type Diep5len = crate::Reg<diep5len::Diep5lenSpec>;
#[doc = "device IN endpoint-5 transfer length register"]
pub mod diep5len;
#[doc = "DOEP1LEN (rw) register accessor: device OUT endpoint-1 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep1len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep1len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep1len`]
module"]
#[doc(alias = "DOEP1LEN")]
pub type Doep1len = crate::Reg<doep1len::Doep1lenSpec>;
#[doc = "device OUT endpoint-1 transfer length register"]
pub mod doep1len;
#[doc = "DOEP2LEN (rw) register accessor: device OUT endpoint-2 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep2len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep2len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep2len`]
module"]
#[doc(alias = "DOEP2LEN")]
pub type Doep2len = crate::Reg<doep2len::Doep2lenSpec>;
#[doc = "device OUT endpoint-2 transfer length register"]
pub mod doep2len;
#[doc = "DOEP3LEN (rw) register accessor: device OUT endpoint-3 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep3len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep3len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep3len`]
module"]
#[doc(alias = "DOEP3LEN")]
pub type Doep3len = crate::Reg<doep3len::Doep3lenSpec>;
#[doc = "device OUT endpoint-3 transfer length register"]
pub mod doep3len;
#[doc = "DOEP4LEN (rw) register accessor: device OUT endpoint-4 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep4len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep4len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep4len`]
module"]
#[doc(alias = "DOEP4LEN")]
pub type Doep4len = crate::Reg<doep4len::Doep4lenSpec>;
#[doc = "device OUT endpoint-4 transfer length register"]
pub mod doep4len;
#[doc = "DOEP5LEN (rw) register accessor: device OUT endpoint-5 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep5len::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep5len::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep5len`]
module"]
#[doc(alias = "DOEP5LEN")]
pub type Doep5len = crate::Reg<doep5len::Doep5lenSpec>;
#[doc = "device OUT endpoint-5 transfer length register"]
pub mod doep5len;
#[doc = "DIEP0DMAADDR (rw) register accessor: Device IN endpoint 0 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep0dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep0dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep0dmaaddr`]
module"]
#[doc(alias = "DIEP0DMAADDR")]
pub type Diep0dmaaddr = crate::Reg<diep0dmaaddr::Diep0dmaaddrSpec>;
#[doc = "Device IN endpoint 0 DMA address register"]
pub mod diep0dmaaddr;
#[doc = "DIEP1DMAADDR (rw) register accessor: Device IN endpoint 1 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep1dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep1dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep1dmaaddr`]
module"]
#[doc(alias = "DIEP1DMAADDR")]
pub type Diep1dmaaddr = crate::Reg<diep1dmaaddr::Diep1dmaaddrSpec>;
#[doc = "Device IN endpoint 1 DMA address register"]
pub mod diep1dmaaddr;
#[doc = "DIEP2DMAADDR (rw) register accessor: Device IN endpoint 2 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep2dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep2dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep2dmaaddr`]
module"]
#[doc(alias = "DIEP2DMAADDR")]
pub type Diep2dmaaddr = crate::Reg<diep2dmaaddr::Diep2dmaaddrSpec>;
#[doc = "Device IN endpoint 2 DMA address register"]
pub mod diep2dmaaddr;
#[doc = "DIEP3DMAADDR (rw) register accessor: Device IN endpoint 3 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep3dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep3dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep3dmaaddr`]
module"]
#[doc(alias = "DIEP3DMAADDR")]
pub type Diep3dmaaddr = crate::Reg<diep3dmaaddr::Diep3dmaaddrSpec>;
#[doc = "Device IN endpoint 3 DMA address register"]
pub mod diep3dmaaddr;
#[doc = "DIEP4DMAADDR (rw) register accessor: Device IN endpoint 4 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep4dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep4dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep4dmaaddr`]
module"]
#[doc(alias = "DIEP4DMAADDR")]
pub type Diep4dmaaddr = crate::Reg<diep4dmaaddr::Diep4dmaaddrSpec>;
#[doc = "Device IN endpoint 4 DMA address register"]
pub mod diep4dmaaddr;
#[doc = "DIEP5DMAADDR (rw) register accessor: Device IN endpoint 5 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep5dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep5dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep5dmaaddr`]
module"]
#[doc(alias = "DIEP5DMAADDR")]
pub type Diep5dmaaddr = crate::Reg<diep5dmaaddr::Diep5dmaaddrSpec>;
#[doc = "Device IN endpoint 5 DMA address register"]
pub mod diep5dmaaddr;
#[doc = "DOEP0DMAADDR (rw) register accessor: Device OUT endpoint 0 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep0dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep0dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep0dmaaddr`]
module"]
#[doc(alias = "DOEP0DMAADDR")]
pub type Doep0dmaaddr = crate::Reg<doep0dmaaddr::Doep0dmaaddrSpec>;
#[doc = "Device OUT endpoint 0 DMA address register"]
pub mod doep0dmaaddr;
#[doc = "DOEP1DMAADDR (rw) register accessor: Device OUT endpoint 1 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep1dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep1dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep1dmaaddr`]
module"]
#[doc(alias = "DOEP1DMAADDR")]
pub type Doep1dmaaddr = crate::Reg<doep1dmaaddr::Doep1dmaaddrSpec>;
#[doc = "Device OUT endpoint 1 DMA address register"]
pub mod doep1dmaaddr;
#[doc = "DOEP2DMAADDR (rw) register accessor: Device OUT endpoint 2 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep2dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep2dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep2dmaaddr`]
module"]
#[doc(alias = "DOEP2DMAADDR")]
pub type Doep2dmaaddr = crate::Reg<doep2dmaaddr::Doep2dmaaddrSpec>;
#[doc = "Device OUT endpoint 2 DMA address register"]
pub mod doep2dmaaddr;
#[doc = "DOEP3DMAADDR (rw) register accessor: Device OUT endpoint 3 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep3dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep3dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep3dmaaddr`]
module"]
#[doc(alias = "DOEP3DMAADDR")]
pub type Doep3dmaaddr = crate::Reg<doep3dmaaddr::Doep3dmaaddrSpec>;
#[doc = "Device OUT endpoint 3 DMA address register"]
pub mod doep3dmaaddr;
#[doc = "DOEP4DMAADDR (rw) register accessor: Device OUT endpoint 4 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep4dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep4dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep4dmaaddr`]
module"]
#[doc(alias = "DOEP4DMAADDR")]
pub type Doep4dmaaddr = crate::Reg<doep4dmaaddr::Doep4dmaaddrSpec>;
#[doc = "Device OUT endpoint 4 DMA address register"]
pub mod doep4dmaaddr;
#[doc = "DOEP5DMAADDR (rw) register accessor: Device OUT endpoint 5 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep5dmaaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep5dmaaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@doep5dmaaddr`]
module"]
#[doc(alias = "DOEP5DMAADDR")]
pub type Doep5dmaaddr = crate::Reg<doep5dmaaddr::Doep5dmaaddrSpec>;
#[doc = "Device OUT endpoint 5 DMA address register"]
pub mod doep5dmaaddr;
#[doc = "DIEP0TFSTAT (r) register accessor: device IN endpoint 0 transmit FIFO status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep0tfstat::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep0tfstat`]
module"]
#[doc(alias = "DIEP0TFSTAT")]
pub type Diep0tfstat = crate::Reg<diep0tfstat::Diep0tfstatSpec>;
#[doc = "device IN endpoint 0 transmit FIFO status register"]
pub mod diep0tfstat;
#[doc = "DIEP1TFSTAT (r) register accessor: device IN endpoint 1 transmit FIFO status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep1tfstat::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep1tfstat`]
module"]
#[doc(alias = "DIEP1TFSTAT")]
pub type Diep1tfstat = crate::Reg<diep1tfstat::Diep1tfstatSpec>;
#[doc = "device IN endpoint 1 transmit FIFO status register"]
pub mod diep1tfstat;
#[doc = "DIEP2TFSTAT (r) register accessor: device IN endpoint 2 transmit FIFO status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep2tfstat::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep2tfstat`]
module"]
#[doc(alias = "DIEP2TFSTAT")]
pub type Diep2tfstat = crate::Reg<diep2tfstat::Diep2tfstatSpec>;
#[doc = "device IN endpoint 2 transmit FIFO status register"]
pub mod diep2tfstat;
#[doc = "DIEP3TFSTAT (r) register accessor: device IN endpoint 3 transmit FIFO status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep3tfstat::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep3tfstat`]
module"]
#[doc(alias = "DIEP3TFSTAT")]
pub type Diep3tfstat = crate::Reg<diep3tfstat::Diep3tfstatSpec>;
#[doc = "device IN endpoint 3 transmit FIFO status register"]
pub mod diep3tfstat;
#[doc = "DIEP4TFSTAT (r) register accessor: device IN endpoint 4 transmit FIFO status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep4tfstat::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep4tfstat`]
module"]
#[doc(alias = "DIEP4TFSTAT")]
pub type Diep4tfstat = crate::Reg<diep4tfstat::Diep4tfstatSpec>;
#[doc = "device IN endpoint 4 transmit FIFO status register"]
pub mod diep4tfstat;
#[doc = "DIEP5TFSTAT (r) register accessor: device IN endpoint 5 transmit FIFO status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep5tfstat::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@diep5tfstat`]
module"]
#[doc(alias = "DIEP5TFSTAT")]
pub type Diep5tfstat = crate::Reg<diep5tfstat::Diep5tfstatSpec>;
#[doc = "device IN endpoint 5 transmit FIFO status register"]
pub mod diep5tfstat;
