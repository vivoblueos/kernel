#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    pwrctl: Pwrctl,
    clkctl: Clkctl,
    cmdagmt: Cmdagmt,
    cmdctl: Cmdctl,
    rspcmdidx: Rspcmdidx,
    resp0: Resp0,
    resp1: Resp1,
    resp2: Resp2,
    resp3: Resp3,
    datato: Datato,
    datalen: Datalen,
    datactl: Datactl,
    datacnt: Datacnt,
    stat: Stat,
    intc: Intc,
    inten: Inten,
    _reserved16: [u8; 0x08],
    fifocnt: Fifocnt,
    _reserved17: [u8; 0x34],
    fifo: Fifo,
}
impl RegisterBlock {
    #[doc = "0x00 - Power control register"]
    #[inline(always)]
    pub const fn pwrctl(&self) -> &Pwrctl {
        &self.pwrctl
    }
    #[doc = "0x04 - Clock control register"]
    #[inline(always)]
    pub const fn clkctl(&self) -> &Clkctl {
        &self.clkctl
    }
    #[doc = "0x08 - Command argument register"]
    #[inline(always)]
    pub const fn cmdagmt(&self) -> &Cmdagmt {
        &self.cmdagmt
    }
    #[doc = "0x0c - Command control register"]
    #[inline(always)]
    pub const fn cmdctl(&self) -> &Cmdctl {
        &self.cmdctl
    }
    #[doc = "0x10 - Command index response register"]
    #[inline(always)]
    pub const fn rspcmdidx(&self) -> &Rspcmdidx {
        &self.rspcmdidx
    }
    #[doc = "0x14 - Response register 0"]
    #[inline(always)]
    pub const fn resp0(&self) -> &Resp0 {
        &self.resp0
    }
    #[doc = "0x18 - Response register 1"]
    #[inline(always)]
    pub const fn resp1(&self) -> &Resp1 {
        &self.resp1
    }
    #[doc = "0x1c - Response register 2"]
    #[inline(always)]
    pub const fn resp2(&self) -> &Resp2 {
        &self.resp2
    }
    #[doc = "0x20 - Response register 3"]
    #[inline(always)]
    pub const fn resp3(&self) -> &Resp3 {
        &self.resp3
    }
    #[doc = "0x24 - Data timeout register"]
    #[inline(always)]
    pub const fn datato(&self) -> &Datato {
        &self.datato
    }
    #[doc = "0x28 - Data length register"]
    #[inline(always)]
    pub const fn datalen(&self) -> &Datalen {
        &self.datalen
    }
    #[doc = "0x2c - Data control register"]
    #[inline(always)]
    pub const fn datactl(&self) -> &Datactl {
        &self.datactl
    }
    #[doc = "0x30 - Data counter register"]
    #[inline(always)]
    pub const fn datacnt(&self) -> &Datacnt {
        &self.datacnt
    }
    #[doc = "0x34 - Status register"]
    #[inline(always)]
    pub const fn stat(&self) -> &Stat {
        &self.stat
    }
    #[doc = "0x38 - Interrupt clear register"]
    #[inline(always)]
    pub const fn intc(&self) -> &Intc {
        &self.intc
    }
    #[doc = "0x3c - Interrupt enable register"]
    #[inline(always)]
    pub const fn inten(&self) -> &Inten {
        &self.inten
    }
    #[doc = "0x48 - FIFO counter register"]
    #[inline(always)]
    pub const fn fifocnt(&self) -> &Fifocnt {
        &self.fifocnt
    }
    #[doc = "0x80 - FIFO data register"]
    #[inline(always)]
    pub const fn fifo(&self) -> &Fifo {
        &self.fifo
    }
}
#[doc = "PWRCTL (rw) register accessor: Power control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pwrctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pwrctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pwrctl`]
module"]
#[doc(alias = "PWRCTL")]
pub type Pwrctl = crate::Reg<pwrctl::PwrctlSpec>;
#[doc = "Power control register"]
pub mod pwrctl;
#[doc = "CLKCTL (rw) register accessor: Clock control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`clkctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`clkctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clkctl`]
module"]
#[doc(alias = "CLKCTL")]
pub type Clkctl = crate::Reg<clkctl::ClkctlSpec>;
#[doc = "Clock control register"]
pub mod clkctl;
#[doc = "CMDAGMT (rw) register accessor: Command argument register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cmdagmt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cmdagmt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cmdagmt`]
module"]
#[doc(alias = "CMDAGMT")]
pub type Cmdagmt = crate::Reg<cmdagmt::CmdagmtSpec>;
#[doc = "Command argument register"]
pub mod cmdagmt;
#[doc = "CMDCTL (rw) register accessor: Command control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cmdctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cmdctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cmdctl`]
module"]
#[doc(alias = "CMDCTL")]
pub type Cmdctl = crate::Reg<cmdctl::CmdctlSpec>;
#[doc = "Command control register"]
pub mod cmdctl;
#[doc = "RSPCMDIDX (r) register accessor: Command index response register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rspcmdidx::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rspcmdidx`]
module"]
#[doc(alias = "RSPCMDIDX")]
pub type Rspcmdidx = crate::Reg<rspcmdidx::RspcmdidxSpec>;
#[doc = "Command index response register"]
pub mod rspcmdidx;
#[doc = "RESP0 (r) register accessor: Response register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`resp0::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@resp0`]
module"]
#[doc(alias = "RESP0")]
pub type Resp0 = crate::Reg<resp0::Resp0Spec>;
#[doc = "Response register 0"]
pub mod resp0;
#[doc = "RESP1 (r) register accessor: Response register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`resp1::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@resp1`]
module"]
#[doc(alias = "RESP1")]
pub type Resp1 = crate::Reg<resp1::Resp1Spec>;
#[doc = "Response register 1"]
pub mod resp1;
#[doc = "RESP2 (r) register accessor: Response register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`resp2::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@resp2`]
module"]
#[doc(alias = "RESP2")]
pub type Resp2 = crate::Reg<resp2::Resp2Spec>;
#[doc = "Response register 2"]
pub mod resp2;
#[doc = "RESP3 (r) register accessor: Response register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`resp3::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@resp3`]
module"]
#[doc(alias = "RESP3")]
pub type Resp3 = crate::Reg<resp3::Resp3Spec>;
#[doc = "Response register 3"]
pub mod resp3;
#[doc = "DATATO (rw) register accessor: Data timeout register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`datato::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`datato::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@datato`]
module"]
#[doc(alias = "DATATO")]
pub type Datato = crate::Reg<datato::DatatoSpec>;
#[doc = "Data timeout register"]
pub mod datato;
#[doc = "DATALEN (rw) register accessor: Data length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`datalen::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`datalen::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@datalen`]
module"]
#[doc(alias = "DATALEN")]
pub type Datalen = crate::Reg<datalen::DatalenSpec>;
#[doc = "Data length register"]
pub mod datalen;
#[doc = "DATACTL (rw) register accessor: Data control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`datactl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`datactl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@datactl`]
module"]
#[doc(alias = "DATACTL")]
pub type Datactl = crate::Reg<datactl::DatactlSpec>;
#[doc = "Data control register"]
pub mod datactl;
#[doc = "DATACNT (r) register accessor: Data counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`datacnt::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@datacnt`]
module"]
#[doc(alias = "DATACNT")]
pub type Datacnt = crate::Reg<datacnt::DatacntSpec>;
#[doc = "Data counter register"]
pub mod datacnt;
#[doc = "STAT (r) register accessor: Status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@stat`]
module"]
#[doc(alias = "STAT")]
pub type Stat = crate::Reg<stat::StatSpec>;
#[doc = "Status register"]
pub mod stat;
#[doc = "INTC (w) register accessor: Interrupt clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`intc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@intc`]
module"]
#[doc(alias = "INTC")]
pub type Intc = crate::Reg<intc::IntcSpec>;
#[doc = "Interrupt clear register"]
pub mod intc;
#[doc = "INTEN (rw) register accessor: Interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@inten`]
module"]
#[doc(alias = "INTEN")]
pub type Inten = crate::Reg<inten::IntenSpec>;
#[doc = "Interrupt enable register"]
pub mod inten;
#[doc = "FIFOCNT (r) register accessor: FIFO counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fifocnt::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fifocnt`]
module"]
#[doc(alias = "FIFOCNT")]
pub type Fifocnt = crate::Reg<fifocnt::FifocntSpec>;
#[doc = "FIFO counter register"]
pub mod fifocnt;
#[doc = "FIFO (rw) register accessor: FIFO data register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fifo::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fifo::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fifo`]
module"]
#[doc(alias = "FIFO")]
pub type Fifo = crate::Reg<fifo::FifoSpec>;
#[doc = "FIFO data register"]
pub mod fifo;
