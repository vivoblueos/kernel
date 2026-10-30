#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    intf: Intf,
    intc: Intc,
    ch0ctl: Ch0ctl,
    ch0cnt: Ch0cnt,
    ch0paddr: Ch0paddr,
    ch0maddr: Ch0maddr,
    _reserved6: [u8; 0x04],
    ch1ctl: Ch1ctl,
    ch1cnt: Ch1cnt,
    ch1paddr: Ch1paddr,
    ch1maddr: Ch1maddr,
    _reserved10: [u8; 0x04],
    ch2ctl: Ch2ctl,
    ch2cnt: Ch2cnt,
    ch2paddr: Ch2paddr,
    ch2maddr: Ch2maddr,
    _reserved14: [u8; 0x04],
    ch3ctl: Ch3ctl,
    ch3cnt: Ch3cnt,
    ch3paddr: Ch3paddr,
    ch3maddr: Ch3maddr,
    _reserved18: [u8; 0x04],
    ch4ctl: Ch4ctl,
    ch4cnt: Ch4cnt,
    ch4paddr: Ch4paddr,
    ch4maddr: Ch4maddr,
    _reserved22: [u8; 0x04],
    ch5ctl: Ch5ctl,
    ch5cnt: Ch5cnt,
    ch5paddr: Ch5paddr,
    ch5maddr: Ch5maddr,
    _reserved26: [u8; 0x04],
    ch6ctl: Ch6ctl,
    ch6cnt: Ch6cnt,
    ch6paddr: Ch6paddr,
    ch6maddr: Ch6maddr,
}
impl RegisterBlock {
    #[doc = "0x00 - Interrupt flag register"]
    #[inline(always)]
    pub const fn intf(&self) -> &Intf {
        &self.intf
    }
    #[doc = "0x04 - Interrupt flag clear register"]
    #[inline(always)]
    pub const fn intc(&self) -> &Intc {
        &self.intc
    }
    #[doc = "0x08 - Channel 0 control register"]
    #[inline(always)]
    pub const fn ch0ctl(&self) -> &Ch0ctl {
        &self.ch0ctl
    }
    #[doc = "0x0c - Channel 0 counter register"]
    #[inline(always)]
    pub const fn ch0cnt(&self) -> &Ch0cnt {
        &self.ch0cnt
    }
    #[doc = "0x10 - Channel 0 peripheral base address register"]
    #[inline(always)]
    pub const fn ch0paddr(&self) -> &Ch0paddr {
        &self.ch0paddr
    }
    #[doc = "0x14 - Channel 0 memory base address register"]
    #[inline(always)]
    pub const fn ch0maddr(&self) -> &Ch0maddr {
        &self.ch0maddr
    }
    #[doc = "0x1c - Channel 1 control register"]
    #[inline(always)]
    pub const fn ch1ctl(&self) -> &Ch1ctl {
        &self.ch1ctl
    }
    #[doc = "0x20 - Channel 1 counter register"]
    #[inline(always)]
    pub const fn ch1cnt(&self) -> &Ch1cnt {
        &self.ch1cnt
    }
    #[doc = "0x24 - Channel 1 peripheral base address register"]
    #[inline(always)]
    pub const fn ch1paddr(&self) -> &Ch1paddr {
        &self.ch1paddr
    }
    #[doc = "0x28 - Channel 1 memory base address register"]
    #[inline(always)]
    pub const fn ch1maddr(&self) -> &Ch1maddr {
        &self.ch1maddr
    }
    #[doc = "0x30 - Channel 2 control register"]
    #[inline(always)]
    pub const fn ch2ctl(&self) -> &Ch2ctl {
        &self.ch2ctl
    }
    #[doc = "0x34 - Channel 2 counter register"]
    #[inline(always)]
    pub const fn ch2cnt(&self) -> &Ch2cnt {
        &self.ch2cnt
    }
    #[doc = "0x38 - Channel 2 peripheral base address register"]
    #[inline(always)]
    pub const fn ch2paddr(&self) -> &Ch2paddr {
        &self.ch2paddr
    }
    #[doc = "0x3c - Channel 2 memory base address register"]
    #[inline(always)]
    pub const fn ch2maddr(&self) -> &Ch2maddr {
        &self.ch2maddr
    }
    #[doc = "0x44 - Channel 3 control register"]
    #[inline(always)]
    pub const fn ch3ctl(&self) -> &Ch3ctl {
        &self.ch3ctl
    }
    #[doc = "0x48 - Channel 3 counter register"]
    #[inline(always)]
    pub const fn ch3cnt(&self) -> &Ch3cnt {
        &self.ch3cnt
    }
    #[doc = "0x4c - Channel 3 peripheral base address register"]
    #[inline(always)]
    pub const fn ch3paddr(&self) -> &Ch3paddr {
        &self.ch3paddr
    }
    #[doc = "0x50 - Channel 3 memory base address register"]
    #[inline(always)]
    pub const fn ch3maddr(&self) -> &Ch3maddr {
        &self.ch3maddr
    }
    #[doc = "0x58 - Channel 4 control register"]
    #[inline(always)]
    pub const fn ch4ctl(&self) -> &Ch4ctl {
        &self.ch4ctl
    }
    #[doc = "0x5c - Channel 4 counter register"]
    #[inline(always)]
    pub const fn ch4cnt(&self) -> &Ch4cnt {
        &self.ch4cnt
    }
    #[doc = "0x60 - Channel 4 peripheral base address register"]
    #[inline(always)]
    pub const fn ch4paddr(&self) -> &Ch4paddr {
        &self.ch4paddr
    }
    #[doc = "0x64 - Channel 4 memory base address register"]
    #[inline(always)]
    pub const fn ch4maddr(&self) -> &Ch4maddr {
        &self.ch4maddr
    }
    #[doc = "0x6c - Channel 5 control register"]
    #[inline(always)]
    pub const fn ch5ctl(&self) -> &Ch5ctl {
        &self.ch5ctl
    }
    #[doc = "0x70 - Channel 5 counter register"]
    #[inline(always)]
    pub const fn ch5cnt(&self) -> &Ch5cnt {
        &self.ch5cnt
    }
    #[doc = "0x74 - Channel 5 peripheral base address register"]
    #[inline(always)]
    pub const fn ch5paddr(&self) -> &Ch5paddr {
        &self.ch5paddr
    }
    #[doc = "0x78 - Channel 5 memory base address register"]
    #[inline(always)]
    pub const fn ch5maddr(&self) -> &Ch5maddr {
        &self.ch5maddr
    }
    #[doc = "0x80 - Channel 6 control register"]
    #[inline(always)]
    pub const fn ch6ctl(&self) -> &Ch6ctl {
        &self.ch6ctl
    }
    #[doc = "0x84 - Channel 6 counter register"]
    #[inline(always)]
    pub const fn ch6cnt(&self) -> &Ch6cnt {
        &self.ch6cnt
    }
    #[doc = "0x88 - Channel 6 peripheral base address register"]
    #[inline(always)]
    pub const fn ch6paddr(&self) -> &Ch6paddr {
        &self.ch6paddr
    }
    #[doc = "0x8c - Channel 6 memory base address register"]
    #[inline(always)]
    pub const fn ch6maddr(&self) -> &Ch6maddr {
        &self.ch6maddr
    }
}
#[doc = "INTF (r) register accessor: Interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`intf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@intf`]
module"]
#[doc(alias = "INTF")]
pub type Intf = crate::Reg<intf::IntfSpec>;
#[doc = "Interrupt flag register"]
pub mod intf;
#[doc = "INTC (w) register accessor: Interrupt flag clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`intc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@intc`]
module"]
#[doc(alias = "INTC")]
pub type Intc = crate::Reg<intc::IntcSpec>;
#[doc = "Interrupt flag clear register"]
pub mod intc;
#[doc = "CH0CTL (rw) register accessor: Channel 0 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch0ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch0ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch0ctl`]
module"]
#[doc(alias = "CH0CTL")]
pub type Ch0ctl = crate::Reg<ch0ctl::Ch0ctlSpec>;
#[doc = "Channel 0 control register"]
pub mod ch0ctl;
#[doc = "CH0CNT (rw) register accessor: Channel 0 counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch0cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch0cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch0cnt`]
module"]
#[doc(alias = "CH0CNT")]
pub type Ch0cnt = crate::Reg<ch0cnt::Ch0cntSpec>;
#[doc = "Channel 0 counter register"]
pub mod ch0cnt;
#[doc = "CH0PADDR (rw) register accessor: Channel 0 peripheral base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch0paddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch0paddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch0paddr`]
module"]
#[doc(alias = "CH0PADDR")]
pub type Ch0paddr = crate::Reg<ch0paddr::Ch0paddrSpec>;
#[doc = "Channel 0 peripheral base address register"]
pub mod ch0paddr;
#[doc = "CH0MADDR (rw) register accessor: Channel 0 memory base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch0maddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch0maddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch0maddr`]
module"]
#[doc(alias = "CH0MADDR")]
pub type Ch0maddr = crate::Reg<ch0maddr::Ch0maddrSpec>;
#[doc = "Channel 0 memory base address register"]
pub mod ch0maddr;
#[doc = "CH1CTL (rw) register accessor: Channel 1 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch1ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch1ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch1ctl`]
module"]
#[doc(alias = "CH1CTL")]
pub type Ch1ctl = crate::Reg<ch1ctl::Ch1ctlSpec>;
#[doc = "Channel 1 control register"]
pub mod ch1ctl;
#[doc = "CH1CNT (rw) register accessor: Channel 1 counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch1cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch1cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch1cnt`]
module"]
#[doc(alias = "CH1CNT")]
pub type Ch1cnt = crate::Reg<ch1cnt::Ch1cntSpec>;
#[doc = "Channel 1 counter register"]
pub mod ch1cnt;
#[doc = "CH1PADDR (rw) register accessor: Channel 1 peripheral base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch1paddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch1paddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch1paddr`]
module"]
#[doc(alias = "CH1PADDR")]
pub type Ch1paddr = crate::Reg<ch1paddr::Ch1paddrSpec>;
#[doc = "Channel 1 peripheral base address register"]
pub mod ch1paddr;
#[doc = "CH1MADDR (rw) register accessor: Channel 1 memory base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch1maddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch1maddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch1maddr`]
module"]
#[doc(alias = "CH1MADDR")]
pub type Ch1maddr = crate::Reg<ch1maddr::Ch1maddrSpec>;
#[doc = "Channel 1 memory base address register"]
pub mod ch1maddr;
#[doc = "CH2CTL (rw) register accessor: Channel 2 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch2ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch2ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch2ctl`]
module"]
#[doc(alias = "CH2CTL")]
pub type Ch2ctl = crate::Reg<ch2ctl::Ch2ctlSpec>;
#[doc = "Channel 2 control register"]
pub mod ch2ctl;
#[doc = "CH2CNT (rw) register accessor: Channel 2 counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch2cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch2cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch2cnt`]
module"]
#[doc(alias = "CH2CNT")]
pub type Ch2cnt = crate::Reg<ch2cnt::Ch2cntSpec>;
#[doc = "Channel 2 counter register"]
pub mod ch2cnt;
#[doc = "CH2PADDR (rw) register accessor: Channel 2 peripheral base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch2paddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch2paddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch2paddr`]
module"]
#[doc(alias = "CH2PADDR")]
pub type Ch2paddr = crate::Reg<ch2paddr::Ch2paddrSpec>;
#[doc = "Channel 2 peripheral base address register"]
pub mod ch2paddr;
#[doc = "CH2MADDR (rw) register accessor: Channel 2 memory base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch2maddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch2maddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch2maddr`]
module"]
#[doc(alias = "CH2MADDR")]
pub type Ch2maddr = crate::Reg<ch2maddr::Ch2maddrSpec>;
#[doc = "Channel 2 memory base address register"]
pub mod ch2maddr;
#[doc = "CH3CTL (rw) register accessor: Channel 3 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch3ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch3ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch3ctl`]
module"]
#[doc(alias = "CH3CTL")]
pub type Ch3ctl = crate::Reg<ch3ctl::Ch3ctlSpec>;
#[doc = "Channel 3 control register"]
pub mod ch3ctl;
#[doc = "CH3CNT (rw) register accessor: Channel 3 counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch3cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch3cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch3cnt`]
module"]
#[doc(alias = "CH3CNT")]
pub type Ch3cnt = crate::Reg<ch3cnt::Ch3cntSpec>;
#[doc = "Channel 3 counter register"]
pub mod ch3cnt;
#[doc = "CH3PADDR (rw) register accessor: Channel 3 peripheral base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch3paddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch3paddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch3paddr`]
module"]
#[doc(alias = "CH3PADDR")]
pub type Ch3paddr = crate::Reg<ch3paddr::Ch3paddrSpec>;
#[doc = "Channel 3 peripheral base address register"]
pub mod ch3paddr;
#[doc = "CH3MADDR (rw) register accessor: Channel 3 memory base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch3maddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch3maddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch3maddr`]
module"]
#[doc(alias = "CH3MADDR")]
pub type Ch3maddr = crate::Reg<ch3maddr::Ch3maddrSpec>;
#[doc = "Channel 3 memory base address register"]
pub mod ch3maddr;
#[doc = "CH4CTL (rw) register accessor: Channel 4 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch4ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch4ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch4ctl`]
module"]
#[doc(alias = "CH4CTL")]
pub type Ch4ctl = crate::Reg<ch4ctl::Ch4ctlSpec>;
#[doc = "Channel 4 control register"]
pub mod ch4ctl;
#[doc = "CH4CNT (rw) register accessor: Channel 4 counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch4cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch4cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch4cnt`]
module"]
#[doc(alias = "CH4CNT")]
pub type Ch4cnt = crate::Reg<ch4cnt::Ch4cntSpec>;
#[doc = "Channel 4 counter register"]
pub mod ch4cnt;
#[doc = "CH4PADDR (rw) register accessor: Channel 4 peripheral base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch4paddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch4paddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch4paddr`]
module"]
#[doc(alias = "CH4PADDR")]
pub type Ch4paddr = crate::Reg<ch4paddr::Ch4paddrSpec>;
#[doc = "Channel 4 peripheral base address register"]
pub mod ch4paddr;
#[doc = "CH4MADDR (rw) register accessor: Channel 4 memory base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch4maddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch4maddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch4maddr`]
module"]
#[doc(alias = "CH4MADDR")]
pub type Ch4maddr = crate::Reg<ch4maddr::Ch4maddrSpec>;
#[doc = "Channel 4 memory base address register"]
pub mod ch4maddr;
#[doc = "CH5CTL (rw) register accessor: Channel 5 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch5ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch5ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch5ctl`]
module"]
#[doc(alias = "CH5CTL")]
pub type Ch5ctl = crate::Reg<ch5ctl::Ch5ctlSpec>;
#[doc = "Channel 5 control register"]
pub mod ch5ctl;
#[doc = "CH5CNT (rw) register accessor: Channel 5 counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch5cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch5cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch5cnt`]
module"]
#[doc(alias = "CH5CNT")]
pub type Ch5cnt = crate::Reg<ch5cnt::Ch5cntSpec>;
#[doc = "Channel 5 counter register"]
pub mod ch5cnt;
#[doc = "CH5PADDR (rw) register accessor: Channel 5 peripheral base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch5paddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch5paddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch5paddr`]
module"]
#[doc(alias = "CH5PADDR")]
pub type Ch5paddr = crate::Reg<ch5paddr::Ch5paddrSpec>;
#[doc = "Channel 5 peripheral base address register"]
pub mod ch5paddr;
#[doc = "CH5MADDR (rw) register accessor: Channel 5 memory base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch5maddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch5maddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch5maddr`]
module"]
#[doc(alias = "CH5MADDR")]
pub type Ch5maddr = crate::Reg<ch5maddr::Ch5maddrSpec>;
#[doc = "Channel 5 memory base address register"]
pub mod ch5maddr;
#[doc = "CH6CTL (rw) register accessor: Channel 6 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch6ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch6ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch6ctl`]
module"]
#[doc(alias = "CH6CTL")]
pub type Ch6ctl = crate::Reg<ch6ctl::Ch6ctlSpec>;
#[doc = "Channel 6 control register"]
pub mod ch6ctl;
#[doc = "CH6CNT (rw) register accessor: Channel 6 counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch6cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch6cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch6cnt`]
module"]
#[doc(alias = "CH6CNT")]
pub type Ch6cnt = crate::Reg<ch6cnt::Ch6cntSpec>;
#[doc = "Channel 6 counter register"]
pub mod ch6cnt;
#[doc = "CH6PADDR (rw) register accessor: Channel 6 peripheral base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch6paddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch6paddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch6paddr`]
module"]
#[doc(alias = "CH6PADDR")]
pub type Ch6paddr = crate::Reg<ch6paddr::Ch6paddrSpec>;
#[doc = "Channel 6 peripheral base address register"]
pub mod ch6paddr;
#[doc = "CH6MADDR (rw) register accessor: Channel 6 memory base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch6maddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch6maddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch6maddr`]
module"]
#[doc(alias = "CH6MADDR")]
pub type Ch6maddr = crate::Reg<ch6maddr::Ch6maddrSpec>;
#[doc = "Channel 6 memory base address register"]
pub mod ch6maddr;
