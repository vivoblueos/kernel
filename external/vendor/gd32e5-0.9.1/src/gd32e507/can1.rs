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
