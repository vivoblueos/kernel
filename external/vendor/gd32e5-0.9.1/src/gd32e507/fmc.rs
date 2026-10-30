#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    ws: Ws,
    key: Key,
    obkey: Obkey,
    stat: Stat,
    ctl: Ctl,
    addr: Addr,
    _reserved6: [u8; 0x04],
    obstat: Obstat,
    wp: Wp,
    _reserved8: [u8; 0xdc],
    pid: Pid,
}
impl RegisterBlock {
    #[doc = "0x00 - wait state counter register"]
    #[inline(always)]
    pub const fn ws(&self) -> &Ws {
        &self.ws
    }
    #[doc = "0x04 - Unlock key register"]
    #[inline(always)]
    pub const fn key(&self) -> &Key {
        &self.key
    }
    #[doc = "0x08 - Option byte unlock key register"]
    #[inline(always)]
    pub const fn obkey(&self) -> &Obkey {
        &self.obkey
    }
    #[doc = "0x0c - Status register"]
    #[inline(always)]
    pub const fn stat(&self) -> &Stat {
        &self.stat
    }
    #[doc = "0x10 - Control register"]
    #[inline(always)]
    pub const fn ctl(&self) -> &Ctl {
        &self.ctl
    }
    #[doc = "0x14 - Address register"]
    #[inline(always)]
    pub const fn addr(&self) -> &Addr {
        &self.addr
    }
    #[doc = "0x1c - Option byte status register"]
    #[inline(always)]
    pub const fn obstat(&self) -> &Obstat {
        &self.obstat
    }
    #[doc = "0x20 - Erase/Program Protection register"]
    #[inline(always)]
    pub const fn wp(&self) -> &Wp {
        &self.wp
    }
    #[doc = "0x100 - Product ID register"]
    #[inline(always)]
    pub const fn pid(&self) -> &Pid {
        &self.pid
    }
}
#[doc = "WS (rw) register accessor: wait state counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ws::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ws::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ws`]
module"]
#[doc(alias = "WS")]
pub type Ws = crate::Reg<ws::WsSpec>;
#[doc = "wait state counter register"]
pub mod ws;
#[doc = "KEY (w) register accessor: Unlock key register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`key::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@key`]
module"]
#[doc(alias = "KEY")]
pub type Key = crate::Reg<key::KeySpec>;
#[doc = "Unlock key register"]
pub mod key;
#[doc = "OBKEY (w) register accessor: Option byte unlock key register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`obkey::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@obkey`]
module"]
#[doc(alias = "OBKEY")]
pub type Obkey = crate::Reg<obkey::ObkeySpec>;
#[doc = "Option byte unlock key register"]
pub mod obkey;
#[doc = "STAT (rw) register accessor: Status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`stat::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@stat`]
module"]
#[doc(alias = "STAT")]
pub type Stat = crate::Reg<stat::StatSpec>;
#[doc = "Status register"]
pub mod stat;
#[doc = "CTL (rw) register accessor: Control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl`]
module"]
#[doc(alias = "CTL")]
pub type Ctl = crate::Reg<ctl::CtlSpec>;
#[doc = "Control register"]
pub mod ctl;
#[doc = "ADDR (w) register accessor: Address register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`addr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@addr`]
module"]
#[doc(alias = "ADDR")]
pub type Addr = crate::Reg<addr::AddrSpec>;
#[doc = "Address register"]
pub mod addr;
#[doc = "OBSTAT (r) register accessor: Option byte status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`obstat::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@obstat`]
module"]
#[doc(alias = "OBSTAT")]
pub type Obstat = crate::Reg<obstat::ObstatSpec>;
#[doc = "Option byte status register"]
pub mod obstat;
#[doc = "WP (r) register accessor: Erase/Program Protection register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`wp::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wp`]
module"]
#[doc(alias = "WP")]
pub type Wp = crate::Reg<wp::WpSpec>;
#[doc = "Erase/Program Protection register"]
pub mod wp;
#[doc = "PID (r) register accessor: Product ID register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pid::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pid`]
module"]
#[doc(alias = "PID")]
pub type Pid = crate::Reg<pid::PidSpec>;
#[doc = "Product ID register"]
pub mod pid;
