#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    ctl: Ctl,
    stat: Stat,
    tstat: Tstat,
    rfifo0: Rfifo0,
    rfifo1: Rfifo1,
    inten: Inten,
    err: Err,
    bt: Bt,
    _reserved8: [u8; 0x0160],
    tmi0: Tmi0,
    tmp0: Tmp0,
    tmdata00: Tmdata00,
    tmdata10: Tmdata10,
    tmi1: Tmi1,
    tmp1: Tmp1,
    tmdata01: Tmdata01,
    tmdata11: Tmdata11,
    tmi2: Tmi2,
    tmp2: Tmp2,
    tmdata02: Tmdata02,
    tmdata12: Tmdata12,
    rfifomi0: Rfifomi0,
    rfifomp0: Rfifomp0,
    rfifomdata00: Rfifomdata00,
    rfifomdata10: Rfifomdata10,
    rfifomi1: Rfifomi1,
    rfifomp1: Rfifomp1,
    rfifomdata01: Rfifomdata01,
    rfifomdata11: Rfifomdata11,
    _reserved28: [u8; 0x30],
    fctl: Fctl,
    fmcfg: Fmcfg,
    _reserved30: [u8; 0x04],
    fscfg: Fscfg,
    _reserved31: [u8; 0x04],
    fafifo: Fafifo,
    _reserved32: [u8; 0x04],
    fw: Fw,
    _reserved33: [u8; 0x20],
    f0data0: F0data0,
    f0data1: F0data1,
    f1data0: F1data0,
    f1data1: F1data1,
    f2data0: F2data0,
    f2data1: F2data1,
    f3data0: F3data0,
    f3data1: F3data1,
    f4data0: F4data0,
    f4data1: F4data1,
    f5data0: F5data0,
    f5data1: F5data1,
    f6data0: F6data0,
    f6data1: F6data1,
    f7data0: F7data0,
    f7data1: F7data1,
    f8data0: F8data0,
    f8data1: F8data1,
    f9data0: F9data0,
    f9data1: F9data1,
    f10data0: F10data0,
    f10data1: F10data1,
    f11data0: F11data0,
    f11data1: F11data1,
    f12data0: F12data0,
    f12data1: F12data1,
    f13data0: F13data0,
    f13data1: F13data1,
    f14data0: F14data0,
    f14data1: F14data1,
    f15data0: F15data0,
    f15data1: F15data1,
    f16data0: F16data0,
    f16data1: F16data1,
    f17data0: F17data0,
    f17data1: F17data1,
    f18data0: F18data0,
    f18data1: F18data1,
    f19data0: F19data0,
    f19data1: F19data1,
    f20data0: F20data0,
    f20data1: F20data1,
    f21data0: F21data0,
    f21data1: F21data1,
    f22data0: F22data0,
    f22data1: F22data1,
    f23data0: F23data0,
    f23data1: F23data1,
    f24data0: F24data0,
    f24data1: F24data1,
    f25data0: F25data0,
    f25data1: F25data1,
    f26data0: F26data0,
    f26data1: F26data1,
    f27data0: F27data0,
    f27data1: F27data1,
}
impl RegisterBlock {
    #[doc = "0x00 - Control register"]
    #[inline(always)]
    pub const fn ctl(&self) -> &Ctl {
        &self.ctl
    }
    #[doc = "0x04 - Status register"]
    #[inline(always)]
    pub const fn stat(&self) -> &Stat {
        &self.stat
    }
    #[doc = "0x08 - Transmit status register"]
    #[inline(always)]
    pub const fn tstat(&self) -> &Tstat {
        &self.tstat
    }
    #[doc = "0x0c - Receive message FIFO0 register"]
    #[inline(always)]
    pub const fn rfifo0(&self) -> &Rfifo0 {
        &self.rfifo0
    }
    #[doc = "0x10 - Receive message FIFO1 register"]
    #[inline(always)]
    pub const fn rfifo1(&self) -> &Rfifo1 {
        &self.rfifo1
    }
    #[doc = "0x14 - Interrupt enable register"]
    #[inline(always)]
    pub const fn inten(&self) -> &Inten {
        &self.inten
    }
    #[doc = "0x18 - Error register"]
    #[inline(always)]
    pub const fn err(&self) -> &Err {
        &self.err
    }
    #[doc = "0x1c - Bit timing register"]
    #[inline(always)]
    pub const fn bt(&self) -> &Bt {
        &self.bt
    }
    #[doc = "0x180 - Transmit mailbox identifier register 0"]
    #[inline(always)]
    pub const fn tmi0(&self) -> &Tmi0 {
        &self.tmi0
    }
    #[doc = "0x184 - Transmit mailbox property register 0"]
    #[inline(always)]
    pub const fn tmp0(&self) -> &Tmp0 {
        &self.tmp0
    }
    #[doc = "0x188 - Transmit mailbox data0 register"]
    #[inline(always)]
    pub const fn tmdata00(&self) -> &Tmdata00 {
        &self.tmdata00
    }
    #[doc = "0x18c - Transmit mailbox data1 register"]
    #[inline(always)]
    pub const fn tmdata10(&self) -> &Tmdata10 {
        &self.tmdata10
    }
    #[doc = "0x190 - Transmit mailbox identifier register 1"]
    #[inline(always)]
    pub const fn tmi1(&self) -> &Tmi1 {
        &self.tmi1
    }
    #[doc = "0x194 - Transmit mailbox property register 1"]
    #[inline(always)]
    pub const fn tmp1(&self) -> &Tmp1 {
        &self.tmp1
    }
    #[doc = "0x198 - Transmit mailbox data0 register"]
    #[inline(always)]
    pub const fn tmdata01(&self) -> &Tmdata01 {
        &self.tmdata01
    }
    #[doc = "0x19c - Transmit mailbox data1 register"]
    #[inline(always)]
    pub const fn tmdata11(&self) -> &Tmdata11 {
        &self.tmdata11
    }
    #[doc = "0x1a0 - Transmit mailbox identifier register 2"]
    #[inline(always)]
    pub const fn tmi2(&self) -> &Tmi2 {
        &self.tmi2
    }
    #[doc = "0x1a4 - Transmit mailbox property register 2"]
    #[inline(always)]
    pub const fn tmp2(&self) -> &Tmp2 {
        &self.tmp2
    }
    #[doc = "0x1a8 - Transmit mailbox data0 register"]
    #[inline(always)]
    pub const fn tmdata02(&self) -> &Tmdata02 {
        &self.tmdata02
    }
    #[doc = "0x1ac - Transmit mailbox data1 register"]
    #[inline(always)]
    pub const fn tmdata12(&self) -> &Tmdata12 {
        &self.tmdata12
    }
    #[doc = "0x1b0 - Receive FIFO mailbox identifier register"]
    #[inline(always)]
    pub const fn rfifomi0(&self) -> &Rfifomi0 {
        &self.rfifomi0
    }
    #[doc = "0x1b4 - Receive FIFO0 mailbox property register"]
    #[inline(always)]
    pub const fn rfifomp0(&self) -> &Rfifomp0 {
        &self.rfifomp0
    }
    #[doc = "0x1b8 - Receive FIFO0 mailbox data0 register"]
    #[inline(always)]
    pub const fn rfifomdata00(&self) -> &Rfifomdata00 {
        &self.rfifomdata00
    }
    #[doc = "0x1bc - Receive FIFO0 mailbox data1 register"]
    #[inline(always)]
    pub const fn rfifomdata10(&self) -> &Rfifomdata10 {
        &self.rfifomdata10
    }
    #[doc = "0x1c0 - Receive FIFO1 mailbox identifier register"]
    #[inline(always)]
    pub const fn rfifomi1(&self) -> &Rfifomi1 {
        &self.rfifomi1
    }
    #[doc = "0x1c4 - Receive FIFO1 mailbox property register"]
    #[inline(always)]
    pub const fn rfifomp1(&self) -> &Rfifomp1 {
        &self.rfifomp1
    }
    #[doc = "0x1c8 - Receive FIFO1 mailbox data0 register"]
    #[inline(always)]
    pub const fn rfifomdata01(&self) -> &Rfifomdata01 {
        &self.rfifomdata01
    }
    #[doc = "0x1cc - Receive FIFO1 mailbox data1 register"]
    #[inline(always)]
    pub const fn rfifomdata11(&self) -> &Rfifomdata11 {
        &self.rfifomdata11
    }
    #[doc = "0x200 - Filter control register"]
    #[inline(always)]
    pub const fn fctl(&self) -> &Fctl {
        &self.fctl
    }
    #[doc = "0x204 - Filter mode configuration register"]
    #[inline(always)]
    pub const fn fmcfg(&self) -> &Fmcfg {
        &self.fmcfg
    }
    #[doc = "0x20c - Filter scale configuration register"]
    #[inline(always)]
    pub const fn fscfg(&self) -> &Fscfg {
        &self.fscfg
    }
    #[doc = "0x214 - Filter associated FIFO register"]
    #[inline(always)]
    pub const fn fafifo(&self) -> &Fafifo {
        &self.fafifo
    }
    #[doc = "0x21c - Filter working register"]
    #[inline(always)]
    pub const fn fw(&self) -> &Fw {
        &self.fw
    }
    #[doc = "0x240 - Filter 0 data 0 register"]
    #[inline(always)]
    pub const fn f0data0(&self) -> &F0data0 {
        &self.f0data0
    }
    #[doc = "0x244 - Filter 0 data 1 register"]
    #[inline(always)]
    pub const fn f0data1(&self) -> &F0data1 {
        &self.f0data1
    }
    #[doc = "0x248 - Filter 1 data 0 register"]
    #[inline(always)]
    pub const fn f1data0(&self) -> &F1data0 {
        &self.f1data0
    }
    #[doc = "0x24c - Filter 1 data 1 register"]
    #[inline(always)]
    pub const fn f1data1(&self) -> &F1data1 {
        &self.f1data1
    }
    #[doc = "0x250 - Filter 2 data 0 register"]
    #[inline(always)]
    pub const fn f2data0(&self) -> &F2data0 {
        &self.f2data0
    }
    #[doc = "0x254 - Filter 2 data 1 register"]
    #[inline(always)]
    pub const fn f2data1(&self) -> &F2data1 {
        &self.f2data1
    }
    #[doc = "0x258 - Filter 3 data 0 register"]
    #[inline(always)]
    pub const fn f3data0(&self) -> &F3data0 {
        &self.f3data0
    }
    #[doc = "0x25c - Filter 3 data 1 register"]
    #[inline(always)]
    pub const fn f3data1(&self) -> &F3data1 {
        &self.f3data1
    }
    #[doc = "0x260 - Filter 4 data 0 register"]
    #[inline(always)]
    pub const fn f4data0(&self) -> &F4data0 {
        &self.f4data0
    }
    #[doc = "0x264 - Filter 4 data 1 register"]
    #[inline(always)]
    pub const fn f4data1(&self) -> &F4data1 {
        &self.f4data1
    }
    #[doc = "0x268 - Filter 5 data 0 register"]
    #[inline(always)]
    pub const fn f5data0(&self) -> &F5data0 {
        &self.f5data0
    }
    #[doc = "0x26c - Filter 5 data 1 register"]
    #[inline(always)]
    pub const fn f5data1(&self) -> &F5data1 {
        &self.f5data1
    }
    #[doc = "0x270 - Filter 6 data 0 register"]
    #[inline(always)]
    pub const fn f6data0(&self) -> &F6data0 {
        &self.f6data0
    }
    #[doc = "0x274 - Filter 6 data 1 register"]
    #[inline(always)]
    pub const fn f6data1(&self) -> &F6data1 {
        &self.f6data1
    }
    #[doc = "0x278 - Filter 7 data 0 register"]
    #[inline(always)]
    pub const fn f7data0(&self) -> &F7data0 {
        &self.f7data0
    }
    #[doc = "0x27c - Filter 7 data 1 register"]
    #[inline(always)]
    pub const fn f7data1(&self) -> &F7data1 {
        &self.f7data1
    }
    #[doc = "0x280 - Filter 8 data 0 register"]
    #[inline(always)]
    pub const fn f8data0(&self) -> &F8data0 {
        &self.f8data0
    }
    #[doc = "0x284 - Filter 8 data 1 register"]
    #[inline(always)]
    pub const fn f8data1(&self) -> &F8data1 {
        &self.f8data1
    }
    #[doc = "0x288 - Filter 9 data 0 register"]
    #[inline(always)]
    pub const fn f9data0(&self) -> &F9data0 {
        &self.f9data0
    }
    #[doc = "0x28c - Filter 9 data 1 register"]
    #[inline(always)]
    pub const fn f9data1(&self) -> &F9data1 {
        &self.f9data1
    }
    #[doc = "0x290 - Filter 10 data 0 register"]
    #[inline(always)]
    pub const fn f10data0(&self) -> &F10data0 {
        &self.f10data0
    }
    #[doc = "0x294 - Filter 10 data 1 register"]
    #[inline(always)]
    pub const fn f10data1(&self) -> &F10data1 {
        &self.f10data1
    }
    #[doc = "0x298 - Filter 11 data 0 register"]
    #[inline(always)]
    pub const fn f11data0(&self) -> &F11data0 {
        &self.f11data0
    }
    #[doc = "0x29c - Filter 11 data 1 register"]
    #[inline(always)]
    pub const fn f11data1(&self) -> &F11data1 {
        &self.f11data1
    }
    #[doc = "0x2a0 - Filter 12 data 0 register"]
    #[inline(always)]
    pub const fn f12data0(&self) -> &F12data0 {
        &self.f12data0
    }
    #[doc = "0x2a4 - Filter 12 data 1 register"]
    #[inline(always)]
    pub const fn f12data1(&self) -> &F12data1 {
        &self.f12data1
    }
    #[doc = "0x2a8 - Filter 13 data 0 register"]
    #[inline(always)]
    pub const fn f13data0(&self) -> &F13data0 {
        &self.f13data0
    }
    #[doc = "0x2ac - Filter 13 data 1 register"]
    #[inline(always)]
    pub const fn f13data1(&self) -> &F13data1 {
        &self.f13data1
    }
    #[doc = "0x2b0 - Filter 14 data 0 register"]
    #[inline(always)]
    pub const fn f14data0(&self) -> &F14data0 {
        &self.f14data0
    }
    #[doc = "0x2b4 - Filter 14 data 1 register"]
    #[inline(always)]
    pub const fn f14data1(&self) -> &F14data1 {
        &self.f14data1
    }
    #[doc = "0x2b8 - Filter 15 data 0 register"]
    #[inline(always)]
    pub const fn f15data0(&self) -> &F15data0 {
        &self.f15data0
    }
    #[doc = "0x2bc - Filter 15 data 1 register"]
    #[inline(always)]
    pub const fn f15data1(&self) -> &F15data1 {
        &self.f15data1
    }
    #[doc = "0x2c0 - Filter 16 data 0 register"]
    #[inline(always)]
    pub const fn f16data0(&self) -> &F16data0 {
        &self.f16data0
    }
    #[doc = "0x2c4 - Filter 16 data 1 register"]
    #[inline(always)]
    pub const fn f16data1(&self) -> &F16data1 {
        &self.f16data1
    }
    #[doc = "0x2c8 - Filter 17 data 0 register"]
    #[inline(always)]
    pub const fn f17data0(&self) -> &F17data0 {
        &self.f17data0
    }
    #[doc = "0x2cc - Filter 17 data 1 register"]
    #[inline(always)]
    pub const fn f17data1(&self) -> &F17data1 {
        &self.f17data1
    }
    #[doc = "0x2d0 - Filter 18 data 0 register"]
    #[inline(always)]
    pub const fn f18data0(&self) -> &F18data0 {
        &self.f18data0
    }
    #[doc = "0x2d4 - Filter 18 data 1 register"]
    #[inline(always)]
    pub const fn f18data1(&self) -> &F18data1 {
        &self.f18data1
    }
    #[doc = "0x2d8 - Filter 19 data 0 register"]
    #[inline(always)]
    pub const fn f19data0(&self) -> &F19data0 {
        &self.f19data0
    }
    #[doc = "0x2dc - Filter 19 data 1 register"]
    #[inline(always)]
    pub const fn f19data1(&self) -> &F19data1 {
        &self.f19data1
    }
    #[doc = "0x2e0 - Filter 20 data 0 register"]
    #[inline(always)]
    pub const fn f20data0(&self) -> &F20data0 {
        &self.f20data0
    }
    #[doc = "0x2e4 - Filter 20 data 1 register"]
    #[inline(always)]
    pub const fn f20data1(&self) -> &F20data1 {
        &self.f20data1
    }
    #[doc = "0x2e8 - Filter 21 data 0 register"]
    #[inline(always)]
    pub const fn f21data0(&self) -> &F21data0 {
        &self.f21data0
    }
    #[doc = "0x2ec - Filter 21 data 1 register"]
    #[inline(always)]
    pub const fn f21data1(&self) -> &F21data1 {
        &self.f21data1
    }
    #[doc = "0x2f0 - Filter 22 data 0 register"]
    #[inline(always)]
    pub const fn f22data0(&self) -> &F22data0 {
        &self.f22data0
    }
    #[doc = "0x2f4 - Filter 22 data 1 register"]
    #[inline(always)]
    pub const fn f22data1(&self) -> &F22data1 {
        &self.f22data1
    }
    #[doc = "0x2f8 - Filter 23 data 0 register"]
    #[inline(always)]
    pub const fn f23data0(&self) -> &F23data0 {
        &self.f23data0
    }
    #[doc = "0x2fc - Filter 23 data 1 register"]
    #[inline(always)]
    pub const fn f23data1(&self) -> &F23data1 {
        &self.f23data1
    }
    #[doc = "0x300 - Filter 24 data 0 register"]
    #[inline(always)]
    pub const fn f24data0(&self) -> &F24data0 {
        &self.f24data0
    }
    #[doc = "0x304 - Filter 24 data 1 register"]
    #[inline(always)]
    pub const fn f24data1(&self) -> &F24data1 {
        &self.f24data1
    }
    #[doc = "0x308 - Filter 25 data 0 register"]
    #[inline(always)]
    pub const fn f25data0(&self) -> &F25data0 {
        &self.f25data0
    }
    #[doc = "0x30c - Filter 25 data 1 register"]
    #[inline(always)]
    pub const fn f25data1(&self) -> &F25data1 {
        &self.f25data1
    }
    #[doc = "0x310 - Filter 26 data 0 register"]
    #[inline(always)]
    pub const fn f26data0(&self) -> &F26data0 {
        &self.f26data0
    }
    #[doc = "0x314 - Filter 26 data 1 register"]
    #[inline(always)]
    pub const fn f26data1(&self) -> &F26data1 {
        &self.f26data1
    }
    #[doc = "0x318 - Filter 27 data 0 register"]
    #[inline(always)]
    pub const fn f27data0(&self) -> &F27data0 {
        &self.f27data0
    }
    #[doc = "0x31c - Filter 27 data 1 register"]
    #[inline(always)]
    pub const fn f27data1(&self) -> &F27data1 {
        &self.f27data1
    }
}
#[doc = "CTL (rw) register accessor: Control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl`]
module"]
#[doc(alias = "CTL")]
pub type Ctl = crate::Reg<ctl::CtlSpec>;
#[doc = "Control register"]
pub mod ctl;
#[doc = "STAT (rw) register accessor: Status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`stat::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@stat`]
module"]
#[doc(alias = "STAT")]
pub type Stat = crate::Reg<stat::StatSpec>;
#[doc = "Status register"]
pub mod stat;
#[doc = "TSTAT (rw) register accessor: Transmit status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tstat::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tstat::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tstat`]
module"]
#[doc(alias = "TSTAT")]
pub type Tstat = crate::Reg<tstat::TstatSpec>;
#[doc = "Transmit status register"]
pub mod tstat;
#[doc = "RFIFO0 (rw) register accessor: Receive message FIFO0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifo0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rfifo0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rfifo0`]
module"]
#[doc(alias = "RFIFO0")]
pub type Rfifo0 = crate::Reg<rfifo0::Rfifo0Spec>;
#[doc = "Receive message FIFO0 register"]
pub mod rfifo0;
#[doc = "RFIFO1 (rw) register accessor: Receive message FIFO1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifo1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rfifo1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rfifo1`]
module"]
#[doc(alias = "RFIFO1")]
pub type Rfifo1 = crate::Reg<rfifo1::Rfifo1Spec>;
#[doc = "Receive message FIFO1 register"]
pub mod rfifo1;
#[doc = "INTEN (rw) register accessor: Interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@inten`]
module"]
#[doc(alias = "INTEN")]
pub type Inten = crate::Reg<inten::IntenSpec>;
#[doc = "Interrupt enable register"]
pub mod inten;
#[doc = "ERR (rw) register accessor: Error register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`err::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`err::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@err`]
module"]
#[doc(alias = "ERR")]
pub type Err = crate::Reg<err::ErrSpec>;
#[doc = "Error register"]
pub mod err;
#[doc = "BT (rw) register accessor: Bit timing register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`bt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bt`]
module"]
#[doc(alias = "BT")]
pub type Bt = crate::Reg<bt::BtSpec>;
#[doc = "Bit timing register"]
pub mod bt;
#[doc = "TMI0 (rw) register accessor: Transmit mailbox identifier register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmi0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmi0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tmi0`]
module"]
#[doc(alias = "TMI0")]
pub type Tmi0 = crate::Reg<tmi0::Tmi0Spec>;
#[doc = "Transmit mailbox identifier register 0"]
pub mod tmi0;
#[doc = "TMP0 (rw) register accessor: Transmit mailbox property register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmp0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmp0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tmp0`]
module"]
#[doc(alias = "TMP0")]
pub type Tmp0 = crate::Reg<tmp0::Tmp0Spec>;
#[doc = "Transmit mailbox property register 0"]
pub mod tmp0;
#[doc = "TMDATA00 (rw) register accessor: Transmit mailbox data0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmdata00::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmdata00::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tmdata00`]
module"]
#[doc(alias = "TMDATA00")]
pub type Tmdata00 = crate::Reg<tmdata00::Tmdata00Spec>;
#[doc = "Transmit mailbox data0 register"]
pub mod tmdata00;
#[doc = "TMDATA10 (rw) register accessor: Transmit mailbox data1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmdata10::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmdata10::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tmdata10`]
module"]
#[doc(alias = "TMDATA10")]
pub type Tmdata10 = crate::Reg<tmdata10::Tmdata10Spec>;
#[doc = "Transmit mailbox data1 register"]
pub mod tmdata10;
#[doc = "TMI1 (rw) register accessor: Transmit mailbox identifier register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmi1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmi1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tmi1`]
module"]
#[doc(alias = "TMI1")]
pub type Tmi1 = crate::Reg<tmi1::Tmi1Spec>;
#[doc = "Transmit mailbox identifier register 1"]
pub mod tmi1;
#[doc = "TMP1 (rw) register accessor: Transmit mailbox property register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmp1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmp1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tmp1`]
module"]
#[doc(alias = "TMP1")]
pub type Tmp1 = crate::Reg<tmp1::Tmp1Spec>;
#[doc = "Transmit mailbox property register 1"]
pub mod tmp1;
#[doc = "TMDATA01 (rw) register accessor: Transmit mailbox data0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmdata01::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmdata01::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tmdata01`]
module"]
#[doc(alias = "TMDATA01")]
pub type Tmdata01 = crate::Reg<tmdata01::Tmdata01Spec>;
#[doc = "Transmit mailbox data0 register"]
pub mod tmdata01;
#[doc = "TMDATA11 (rw) register accessor: Transmit mailbox data1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmdata11::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmdata11::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tmdata11`]
module"]
#[doc(alias = "TMDATA11")]
pub type Tmdata11 = crate::Reg<tmdata11::Tmdata11Spec>;
#[doc = "Transmit mailbox data1 register"]
pub mod tmdata11;
#[doc = "TMI2 (rw) register accessor: Transmit mailbox identifier register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmi2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmi2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tmi2`]
module"]
#[doc(alias = "TMI2")]
pub type Tmi2 = crate::Reg<tmi2::Tmi2Spec>;
#[doc = "Transmit mailbox identifier register 2"]
pub mod tmi2;
#[doc = "TMP2 (rw) register accessor: Transmit mailbox property register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmp2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmp2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tmp2`]
module"]
#[doc(alias = "TMP2")]
pub type Tmp2 = crate::Reg<tmp2::Tmp2Spec>;
#[doc = "Transmit mailbox property register 2"]
pub mod tmp2;
#[doc = "TMDATA02 (rw) register accessor: Transmit mailbox data0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmdata02::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmdata02::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tmdata02`]
module"]
#[doc(alias = "TMDATA02")]
pub type Tmdata02 = crate::Reg<tmdata02::Tmdata02Spec>;
#[doc = "Transmit mailbox data0 register"]
pub mod tmdata02;
#[doc = "TMDATA12 (rw) register accessor: Transmit mailbox data1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmdata12::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmdata12::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tmdata12`]
module"]
#[doc(alias = "TMDATA12")]
pub type Tmdata12 = crate::Reg<tmdata12::Tmdata12Spec>;
#[doc = "Transmit mailbox data1 register"]
pub mod tmdata12;
#[doc = "RFIFOMI0 (r) register accessor: Receive FIFO mailbox identifier register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifomi0::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rfifomi0`]
module"]
#[doc(alias = "RFIFOMI0")]
pub type Rfifomi0 = crate::Reg<rfifomi0::Rfifomi0Spec>;
#[doc = "Receive FIFO mailbox identifier register"]
pub mod rfifomi0;
#[doc = "RFIFOMP0 (r) register accessor: Receive FIFO0 mailbox property register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifomp0::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rfifomp0`]
module"]
#[doc(alias = "RFIFOMP0")]
pub type Rfifomp0 = crate::Reg<rfifomp0::Rfifomp0Spec>;
#[doc = "Receive FIFO0 mailbox property register"]
pub mod rfifomp0;
#[doc = "RFIFOMDATA00 (r) register accessor: Receive FIFO0 mailbox data0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifomdata00::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rfifomdata00`]
module"]
#[doc(alias = "RFIFOMDATA00")]
pub type Rfifomdata00 = crate::Reg<rfifomdata00::Rfifomdata00Spec>;
#[doc = "Receive FIFO0 mailbox data0 register"]
pub mod rfifomdata00;
#[doc = "RFIFOMDATA10 (r) register accessor: Receive FIFO0 mailbox data1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifomdata10::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rfifomdata10`]
module"]
#[doc(alias = "RFIFOMDATA10")]
pub type Rfifomdata10 = crate::Reg<rfifomdata10::Rfifomdata10Spec>;
#[doc = "Receive FIFO0 mailbox data1 register"]
pub mod rfifomdata10;
#[doc = "RFIFOMI1 (r) register accessor: Receive FIFO1 mailbox identifier register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifomi1::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rfifomi1`]
module"]
#[doc(alias = "RFIFOMI1")]
pub type Rfifomi1 = crate::Reg<rfifomi1::Rfifomi1Spec>;
#[doc = "Receive FIFO1 mailbox identifier register"]
pub mod rfifomi1;
#[doc = "RFIFOMP1 (r) register accessor: Receive FIFO1 mailbox property register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifomp1::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rfifomp1`]
module"]
#[doc(alias = "RFIFOMP1")]
pub type Rfifomp1 = crate::Reg<rfifomp1::Rfifomp1Spec>;
#[doc = "Receive FIFO1 mailbox property register"]
pub mod rfifomp1;
#[doc = "RFIFOMDATA01 (r) register accessor: Receive FIFO1 mailbox data0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifomdata01::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rfifomdata01`]
module"]
#[doc(alias = "RFIFOMDATA01")]
pub type Rfifomdata01 = crate::Reg<rfifomdata01::Rfifomdata01Spec>;
#[doc = "Receive FIFO1 mailbox data0 register"]
pub mod rfifomdata01;
#[doc = "RFIFOMDATA11 (r) register accessor: Receive FIFO1 mailbox data1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifomdata11::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rfifomdata11`]
module"]
#[doc(alias = "RFIFOMDATA11")]
pub type Rfifomdata11 = crate::Reg<rfifomdata11::Rfifomdata11Spec>;
#[doc = "Receive FIFO1 mailbox data1 register"]
pub mod rfifomdata11;
#[doc = "FCTL (rw) register accessor: Filter control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fctl`]
module"]
#[doc(alias = "FCTL")]
pub type Fctl = crate::Reg<fctl::FctlSpec>;
#[doc = "Filter control register"]
pub mod fctl;
#[doc = "FMCFG (rw) register accessor: Filter mode configuration register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fmcfg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fmcfg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fmcfg`]
module"]
#[doc(alias = "FMCFG")]
pub type Fmcfg = crate::Reg<fmcfg::FmcfgSpec>;
#[doc = "Filter mode configuration register"]
pub mod fmcfg;
#[doc = "FSCFG (rw) register accessor: Filter scale configuration register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fscfg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fscfg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fscfg`]
module"]
#[doc(alias = "FSCFG")]
pub type Fscfg = crate::Reg<fscfg::FscfgSpec>;
#[doc = "Filter scale configuration register"]
pub mod fscfg;
#[doc = "FAFIFO (rw) register accessor: Filter associated FIFO register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fafifo::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fafifo::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fafifo`]
module"]
#[doc(alias = "FAFIFO")]
pub type Fafifo = crate::Reg<fafifo::FafifoSpec>;
#[doc = "Filter associated FIFO register"]
pub mod fafifo;
#[doc = "FW (rw) register accessor: Filter working register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fw::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fw::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fw`]
module"]
#[doc(alias = "FW")]
pub type Fw = crate::Reg<fw::FwSpec>;
#[doc = "Filter working register"]
pub mod fw;
#[doc = "F0DATA0 (rw) register accessor: Filter 0 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f0data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f0data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f0data0`]
module"]
#[doc(alias = "F0DATA0")]
pub type F0data0 = crate::Reg<f0data0::F0data0Spec>;
#[doc = "Filter 0 data 0 register"]
pub mod f0data0;
#[doc = "F0DATA1 (rw) register accessor: Filter 0 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f0data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f0data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f0data1`]
module"]
#[doc(alias = "F0DATA1")]
pub type F0data1 = crate::Reg<f0data1::F0data1Spec>;
#[doc = "Filter 0 data 1 register"]
pub mod f0data1;
#[doc = "F1DATA0 (rw) register accessor: Filter 1 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f1data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f1data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f1data0`]
module"]
#[doc(alias = "F1DATA0")]
pub type F1data0 = crate::Reg<f1data0::F1data0Spec>;
#[doc = "Filter 1 data 0 register"]
pub mod f1data0;
#[doc = "F1DATA1 (rw) register accessor: Filter 1 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f1data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f1data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f1data1`]
module"]
#[doc(alias = "F1DATA1")]
pub type F1data1 = crate::Reg<f1data1::F1data1Spec>;
#[doc = "Filter 1 data 1 register"]
pub mod f1data1;
#[doc = "F2DATA0 (rw) register accessor: Filter 2 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f2data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f2data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f2data0`]
module"]
#[doc(alias = "F2DATA0")]
pub type F2data0 = crate::Reg<f2data0::F2data0Spec>;
#[doc = "Filter 2 data 0 register"]
pub mod f2data0;
#[doc = "F2DATA1 (rw) register accessor: Filter 2 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f2data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f2data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f2data1`]
module"]
#[doc(alias = "F2DATA1")]
pub type F2data1 = crate::Reg<f2data1::F2data1Spec>;
#[doc = "Filter 2 data 1 register"]
pub mod f2data1;
#[doc = "F3DATA0 (rw) register accessor: Filter 3 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f3data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f3data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f3data0`]
module"]
#[doc(alias = "F3DATA0")]
pub type F3data0 = crate::Reg<f3data0::F3data0Spec>;
#[doc = "Filter 3 data 0 register"]
pub mod f3data0;
#[doc = "F3DATA1 (rw) register accessor: Filter 3 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f3data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f3data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f3data1`]
module"]
#[doc(alias = "F3DATA1")]
pub type F3data1 = crate::Reg<f3data1::F3data1Spec>;
#[doc = "Filter 3 data 1 register"]
pub mod f3data1;
#[doc = "F4DATA0 (rw) register accessor: Filter 4 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f4data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f4data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f4data0`]
module"]
#[doc(alias = "F4DATA0")]
pub type F4data0 = crate::Reg<f4data0::F4data0Spec>;
#[doc = "Filter 4 data 0 register"]
pub mod f4data0;
#[doc = "F4DATA1 (rw) register accessor: Filter 4 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f4data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f4data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f4data1`]
module"]
#[doc(alias = "F4DATA1")]
pub type F4data1 = crate::Reg<f4data1::F4data1Spec>;
#[doc = "Filter 4 data 1 register"]
pub mod f4data1;
#[doc = "F5DATA0 (rw) register accessor: Filter 5 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f5data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f5data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f5data0`]
module"]
#[doc(alias = "F5DATA0")]
pub type F5data0 = crate::Reg<f5data0::F5data0Spec>;
#[doc = "Filter 5 data 0 register"]
pub mod f5data0;
#[doc = "F5DATA1 (rw) register accessor: Filter 5 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f5data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f5data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f5data1`]
module"]
#[doc(alias = "F5DATA1")]
pub type F5data1 = crate::Reg<f5data1::F5data1Spec>;
#[doc = "Filter 5 data 1 register"]
pub mod f5data1;
#[doc = "F6DATA0 (rw) register accessor: Filter 6 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f6data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f6data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f6data0`]
module"]
#[doc(alias = "F6DATA0")]
pub type F6data0 = crate::Reg<f6data0::F6data0Spec>;
#[doc = "Filter 6 data 0 register"]
pub mod f6data0;
#[doc = "F6DATA1 (rw) register accessor: Filter 6 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f6data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f6data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f6data1`]
module"]
#[doc(alias = "F6DATA1")]
pub type F6data1 = crate::Reg<f6data1::F6data1Spec>;
#[doc = "Filter 6 data 1 register"]
pub mod f6data1;
#[doc = "F7DATA0 (rw) register accessor: Filter 7 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f7data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f7data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f7data0`]
module"]
#[doc(alias = "F7DATA0")]
pub type F7data0 = crate::Reg<f7data0::F7data0Spec>;
#[doc = "Filter 7 data 0 register"]
pub mod f7data0;
#[doc = "F7DATA1 (rw) register accessor: Filter 7 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f7data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f7data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f7data1`]
module"]
#[doc(alias = "F7DATA1")]
pub type F7data1 = crate::Reg<f7data1::F7data1Spec>;
#[doc = "Filter 7 data 1 register"]
pub mod f7data1;
#[doc = "F8DATA0 (rw) register accessor: Filter 8 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f8data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f8data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f8data0`]
module"]
#[doc(alias = "F8DATA0")]
pub type F8data0 = crate::Reg<f8data0::F8data0Spec>;
#[doc = "Filter 8 data 0 register"]
pub mod f8data0;
#[doc = "F8DATA1 (rw) register accessor: Filter 8 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f8data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f8data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f8data1`]
module"]
#[doc(alias = "F8DATA1")]
pub type F8data1 = crate::Reg<f8data1::F8data1Spec>;
#[doc = "Filter 8 data 1 register"]
pub mod f8data1;
#[doc = "F9DATA0 (rw) register accessor: Filter 9 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f9data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f9data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f9data0`]
module"]
#[doc(alias = "F9DATA0")]
pub type F9data0 = crate::Reg<f9data0::F9data0Spec>;
#[doc = "Filter 9 data 0 register"]
pub mod f9data0;
#[doc = "F9DATA1 (rw) register accessor: Filter 9 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f9data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f9data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f9data1`]
module"]
#[doc(alias = "F9DATA1")]
pub type F9data1 = crate::Reg<f9data1::F9data1Spec>;
#[doc = "Filter 9 data 1 register"]
pub mod f9data1;
#[doc = "F10DATA0 (rw) register accessor: Filter 10 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f10data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f10data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f10data0`]
module"]
#[doc(alias = "F10DATA0")]
pub type F10data0 = crate::Reg<f10data0::F10data0Spec>;
#[doc = "Filter 10 data 0 register"]
pub mod f10data0;
#[doc = "F10DATA1 (rw) register accessor: Filter 10 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f10data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f10data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f10data1`]
module"]
#[doc(alias = "F10DATA1")]
pub type F10data1 = crate::Reg<f10data1::F10data1Spec>;
#[doc = "Filter 10 data 1 register"]
pub mod f10data1;
#[doc = "F11DATA0 (rw) register accessor: Filter 11 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f11data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f11data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f11data0`]
module"]
#[doc(alias = "F11DATA0")]
pub type F11data0 = crate::Reg<f11data0::F11data0Spec>;
#[doc = "Filter 11 data 0 register"]
pub mod f11data0;
#[doc = "F11DATA1 (rw) register accessor: Filter 11 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f11data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f11data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f11data1`]
module"]
#[doc(alias = "F11DATA1")]
pub type F11data1 = crate::Reg<f11data1::F11data1Spec>;
#[doc = "Filter 11 data 1 register"]
pub mod f11data1;
#[doc = "F12DATA0 (rw) register accessor: Filter 12 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f12data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f12data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f12data0`]
module"]
#[doc(alias = "F12DATA0")]
pub type F12data0 = crate::Reg<f12data0::F12data0Spec>;
#[doc = "Filter 12 data 0 register"]
pub mod f12data0;
#[doc = "F12DATA1 (rw) register accessor: Filter 12 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f12data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f12data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f12data1`]
module"]
#[doc(alias = "F12DATA1")]
pub type F12data1 = crate::Reg<f12data1::F12data1Spec>;
#[doc = "Filter 12 data 1 register"]
pub mod f12data1;
#[doc = "F13DATA0 (rw) register accessor: Filter 13 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f13data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f13data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f13data0`]
module"]
#[doc(alias = "F13DATA0")]
pub type F13data0 = crate::Reg<f13data0::F13data0Spec>;
#[doc = "Filter 13 data 0 register"]
pub mod f13data0;
#[doc = "F13DATA1 (rw) register accessor: Filter 13 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f13data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f13data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f13data1`]
module"]
#[doc(alias = "F13DATA1")]
pub type F13data1 = crate::Reg<f13data1::F13data1Spec>;
#[doc = "Filter 13 data 1 register"]
pub mod f13data1;
#[doc = "F14DATA0 (rw) register accessor: Filter 14 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f14data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f14data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f14data0`]
module"]
#[doc(alias = "F14DATA0")]
pub type F14data0 = crate::Reg<f14data0::F14data0Spec>;
#[doc = "Filter 14 data 0 register"]
pub mod f14data0;
#[doc = "F14DATA1 (rw) register accessor: Filter 14 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f14data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f14data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f14data1`]
module"]
#[doc(alias = "F14DATA1")]
pub type F14data1 = crate::Reg<f14data1::F14data1Spec>;
#[doc = "Filter 14 data 1 register"]
pub mod f14data1;
#[doc = "F15DATA0 (rw) register accessor: Filter 15 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f15data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f15data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f15data0`]
module"]
#[doc(alias = "F15DATA0")]
pub type F15data0 = crate::Reg<f15data0::F15data0Spec>;
#[doc = "Filter 15 data 0 register"]
pub mod f15data0;
#[doc = "F15DATA1 (rw) register accessor: Filter 15 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f15data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f15data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f15data1`]
module"]
#[doc(alias = "F15DATA1")]
pub type F15data1 = crate::Reg<f15data1::F15data1Spec>;
#[doc = "Filter 15 data 1 register"]
pub mod f15data1;
#[doc = "F16DATA0 (rw) register accessor: Filter 16 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f16data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f16data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f16data0`]
module"]
#[doc(alias = "F16DATA0")]
pub type F16data0 = crate::Reg<f16data0::F16data0Spec>;
#[doc = "Filter 16 data 0 register"]
pub mod f16data0;
#[doc = "F16DATA1 (rw) register accessor: Filter 16 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f16data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f16data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f16data1`]
module"]
#[doc(alias = "F16DATA1")]
pub type F16data1 = crate::Reg<f16data1::F16data1Spec>;
#[doc = "Filter 16 data 1 register"]
pub mod f16data1;
#[doc = "F17DATA0 (rw) register accessor: Filter 17 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f17data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f17data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f17data0`]
module"]
#[doc(alias = "F17DATA0")]
pub type F17data0 = crate::Reg<f17data0::F17data0Spec>;
#[doc = "Filter 17 data 0 register"]
pub mod f17data0;
#[doc = "F17DATA1 (rw) register accessor: Filter 17 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f17data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f17data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f17data1`]
module"]
#[doc(alias = "F17DATA1")]
pub type F17data1 = crate::Reg<f17data1::F17data1Spec>;
#[doc = "Filter 17 data 1 register"]
pub mod f17data1;
#[doc = "F18DATA0 (rw) register accessor: Filter 18 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f18data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f18data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f18data0`]
module"]
#[doc(alias = "F18DATA0")]
pub type F18data0 = crate::Reg<f18data0::F18data0Spec>;
#[doc = "Filter 18 data 0 register"]
pub mod f18data0;
#[doc = "F18DATA1 (rw) register accessor: Filter 18 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f18data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f18data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f18data1`]
module"]
#[doc(alias = "F18DATA1")]
pub type F18data1 = crate::Reg<f18data1::F18data1Spec>;
#[doc = "Filter 18 data 1 register"]
pub mod f18data1;
#[doc = "F19DATA0 (rw) register accessor: Filter 19 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f19data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f19data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f19data0`]
module"]
#[doc(alias = "F19DATA0")]
pub type F19data0 = crate::Reg<f19data0::F19data0Spec>;
#[doc = "Filter 19 data 0 register"]
pub mod f19data0;
#[doc = "F19DATA1 (rw) register accessor: Filter 19 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f19data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f19data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f19data1`]
module"]
#[doc(alias = "F19DATA1")]
pub type F19data1 = crate::Reg<f19data1::F19data1Spec>;
#[doc = "Filter 19 data 1 register"]
pub mod f19data1;
#[doc = "F20DATA0 (rw) register accessor: Filter 20 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f20data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f20data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f20data0`]
module"]
#[doc(alias = "F20DATA0")]
pub type F20data0 = crate::Reg<f20data0::F20data0Spec>;
#[doc = "Filter 20 data 0 register"]
pub mod f20data0;
#[doc = "F20DATA1 (rw) register accessor: Filter 20 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f20data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f20data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f20data1`]
module"]
#[doc(alias = "F20DATA1")]
pub type F20data1 = crate::Reg<f20data1::F20data1Spec>;
#[doc = "Filter 20 data 1 register"]
pub mod f20data1;
#[doc = "F21DATA0 (rw) register accessor: Filter 21 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f21data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f21data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f21data0`]
module"]
#[doc(alias = "F21DATA0")]
pub type F21data0 = crate::Reg<f21data0::F21data0Spec>;
#[doc = "Filter 21 data 0 register"]
pub mod f21data0;
#[doc = "F21DATA1 (rw) register accessor: Filter 21 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f21data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f21data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f21data1`]
module"]
#[doc(alias = "F21DATA1")]
pub type F21data1 = crate::Reg<f21data1::F21data1Spec>;
#[doc = "Filter 21 data 1 register"]
pub mod f21data1;
#[doc = "F22DATA0 (rw) register accessor: Filter 22 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f22data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f22data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f22data0`]
module"]
#[doc(alias = "F22DATA0")]
pub type F22data0 = crate::Reg<f22data0::F22data0Spec>;
#[doc = "Filter 22 data 0 register"]
pub mod f22data0;
#[doc = "F22DATA1 (rw) register accessor: Filter 22 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f22data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f22data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f22data1`]
module"]
#[doc(alias = "F22DATA1")]
pub type F22data1 = crate::Reg<f22data1::F22data1Spec>;
#[doc = "Filter 22 data 1 register"]
pub mod f22data1;
#[doc = "F23DATA0 (rw) register accessor: Filter 23 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f23data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f23data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f23data0`]
module"]
#[doc(alias = "F23DATA0")]
pub type F23data0 = crate::Reg<f23data0::F23data0Spec>;
#[doc = "Filter 23 data 0 register"]
pub mod f23data0;
#[doc = "F23DATA1 (rw) register accessor: Filter 23 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f23data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f23data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f23data1`]
module"]
#[doc(alias = "F23DATA1")]
pub type F23data1 = crate::Reg<f23data1::F23data1Spec>;
#[doc = "Filter 23 data 1 register"]
pub mod f23data1;
#[doc = "F24DATA0 (rw) register accessor: Filter 24 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f24data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f24data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f24data0`]
module"]
#[doc(alias = "F24DATA0")]
pub type F24data0 = crate::Reg<f24data0::F24data0Spec>;
#[doc = "Filter 24 data 0 register"]
pub mod f24data0;
#[doc = "F24DATA1 (rw) register accessor: Filter 24 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f24data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f24data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f24data1`]
module"]
#[doc(alias = "F24DATA1")]
pub type F24data1 = crate::Reg<f24data1::F24data1Spec>;
#[doc = "Filter 24 data 1 register"]
pub mod f24data1;
#[doc = "F25DATA0 (rw) register accessor: Filter 25 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f25data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f25data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f25data0`]
module"]
#[doc(alias = "F25DATA0")]
pub type F25data0 = crate::Reg<f25data0::F25data0Spec>;
#[doc = "Filter 25 data 0 register"]
pub mod f25data0;
#[doc = "F25DATA1 (rw) register accessor: Filter 25 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f25data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f25data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f25data1`]
module"]
#[doc(alias = "F25DATA1")]
pub type F25data1 = crate::Reg<f25data1::F25data1Spec>;
#[doc = "Filter 25 data 1 register"]
pub mod f25data1;
#[doc = "F26DATA0 (rw) register accessor: Filter 26 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f26data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f26data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f26data0`]
module"]
#[doc(alias = "F26DATA0")]
pub type F26data0 = crate::Reg<f26data0::F26data0Spec>;
#[doc = "Filter 26 data 0 register"]
pub mod f26data0;
#[doc = "F26DATA1 (rw) register accessor: Filter 26 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f26data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f26data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f26data1`]
module"]
#[doc(alias = "F26DATA1")]
pub type F26data1 = crate::Reg<f26data1::F26data1Spec>;
#[doc = "Filter 26 data 1 register"]
pub mod f26data1;
#[doc = "F27DATA0 (rw) register accessor: Filter 27 data 0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f27data0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f27data0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f27data0`]
module"]
#[doc(alias = "F27DATA0")]
pub type F27data0 = crate::Reg<f27data0::F27data0Spec>;
#[doc = "Filter 27 data 0 register"]
pub mod f27data0;
#[doc = "F27DATA1 (rw) register accessor: Filter 27 data 1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`f27data1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`f27data1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@f27data1`]
module"]
#[doc(alias = "F27DATA1")]
pub type F27data1 = crate::Reg<f27data1::F27data1Spec>;
#[doc = "Filter 27 data 1 register"]
pub mod f27data1;
