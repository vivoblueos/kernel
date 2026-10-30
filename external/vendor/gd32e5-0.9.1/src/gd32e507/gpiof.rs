#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    ctl0: Ctl0,
    ctl1: Ctl1,
    istat: Istat,
    octl: Octl,
    bop: Bop,
    bc: Bc,
    lock: Lock,
    _reserved7: [u8; 0x20],
    spd: Spd,
}
impl RegisterBlock {
    #[doc = "0x00 - port control register 0"]
    #[inline(always)]
    pub const fn ctl0(&self) -> &Ctl0 {
        &self.ctl0
    }
    #[doc = "0x04 - port control register 1"]
    #[inline(always)]
    pub const fn ctl1(&self) -> &Ctl1 {
        &self.ctl1
    }
    #[doc = "0x08 - Port input status register"]
    #[inline(always)]
    pub const fn istat(&self) -> &Istat {
        &self.istat
    }
    #[doc = "0x0c - Port output control register"]
    #[inline(always)]
    pub const fn octl(&self) -> &Octl {
        &self.octl
    }
    #[doc = "0x10 - Port bit operate register"]
    #[inline(always)]
    pub const fn bop(&self) -> &Bop {
        &self.bop
    }
    #[doc = "0x14 - Port bit clear register"]
    #[inline(always)]
    pub const fn bc(&self) -> &Bc {
        &self.bc
    }
    #[doc = "0x18 - GPIO port configuration lock register"]
    #[inline(always)]
    pub const fn lock(&self) -> &Lock {
        &self.lock
    }
    #[doc = "0x3c - Port bit speed register"]
    #[inline(always)]
    pub const fn spd(&self) -> &Spd {
        &self.spd
    }
}
#[doc = "CTL0 (rw) register accessor: port control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl0`]
module"]
#[doc(alias = "CTL0")]
pub type Ctl0 = crate::Reg<ctl0::Ctl0Spec>;
#[doc = "port control register 0"]
pub mod ctl0;
#[doc = "CTL1 (rw) register accessor: port control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl1`]
module"]
#[doc(alias = "CTL1")]
pub type Ctl1 = crate::Reg<ctl1::Ctl1Spec>;
#[doc = "port control register 1"]
pub mod ctl1;
#[doc = "ISTAT (r) register accessor: Port input status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`istat::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@istat`]
module"]
#[doc(alias = "ISTAT")]
pub type Istat = crate::Reg<istat::IstatSpec>;
#[doc = "Port input status register"]
pub mod istat;
#[doc = "OCTL (rw) register accessor: Port output control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`octl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`octl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@octl`]
module"]
#[doc(alias = "OCTL")]
pub type Octl = crate::Reg<octl::OctlSpec>;
#[doc = "Port output control register"]
pub mod octl;
#[doc = "BOP (w) register accessor: Port bit operate register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bop::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bop`]
module"]
#[doc(alias = "BOP")]
pub type Bop = crate::Reg<bop::BopSpec>;
#[doc = "Port bit operate register"]
pub mod bop;
#[doc = "BC (w) register accessor: Port bit clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bc`]
module"]
#[doc(alias = "BC")]
pub type Bc = crate::Reg<bc::BcSpec>;
#[doc = "Port bit clear register"]
pub mod bc;
#[doc = "LOCK (rw) register accessor: GPIO port configuration lock register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`lock::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`lock::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lock`]
module"]
#[doc(alias = "LOCK")]
pub type Lock = crate::Reg<lock::LockSpec>;
#[doc = "GPIO port configuration lock register"]
pub mod lock;
#[doc = "SPD (rw) register accessor: Port bit speed register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`spd::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`spd::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@spd`]
module"]
#[doc(alias = "SPD")]
pub type Spd = crate::Reg<spd::SpdSpec>;
#[doc = "Port bit speed register"]
pub mod spd;
