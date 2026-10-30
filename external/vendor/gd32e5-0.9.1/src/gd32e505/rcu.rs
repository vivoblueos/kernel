#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    ctl: Ctl,
    cfg0: Cfg0,
    int: Int,
    apb2rst: Apb2rst,
    apb1rst: Apb1rst,
    ahben: Ahben,
    apb2en: Apb2en,
    apb1en: Apb1en,
    bdctl: Bdctl,
    rstsck: Rstsck,
    ahbrst: Ahbrst,
    cfg1: Cfg1,
    _reserved12: [u8; 0x04],
    dsv: Dsv,
    _reserved13: [u8; 0x88],
    addctl: Addctl,
    addcfg: Addcfg,
    _reserved15: [u8; 0x04],
    addint: Addint,
    pllssctl: Pllssctl,
    cfg2: Cfg2,
    _reserved18: [u8; 0x08],
    addapb1rst: Addapb1rst,
    addapb1en: Addapb1en,
}
impl RegisterBlock {
    #[doc = "0x00 - Control register"]
    #[inline(always)]
    pub const fn ctl(&self) -> &Ctl {
        &self.ctl
    }
    #[doc = "0x04 - Clock configuration register 0 (RCU_CFG0)"]
    #[inline(always)]
    pub const fn cfg0(&self) -> &Cfg0 {
        &self.cfg0
    }
    #[doc = "0x08 - Clock interrupt register (RCU_INT)"]
    #[inline(always)]
    pub const fn int(&self) -> &Int {
        &self.int
    }
    #[doc = "0x0c - APB2 reset register (RCU_APB2RST)"]
    #[inline(always)]
    pub const fn apb2rst(&self) -> &Apb2rst {
        &self.apb2rst
    }
    #[doc = "0x10 - APB1 reset register (RCU_APB1RST)"]
    #[inline(always)]
    pub const fn apb1rst(&self) -> &Apb1rst {
        &self.apb1rst
    }
    #[doc = "0x14 - AHB enable register"]
    #[inline(always)]
    pub const fn ahben(&self) -> &Ahben {
        &self.ahben
    }
    #[doc = "0x18 - APB2 clock enable register (RCU_APB2EN)"]
    #[inline(always)]
    pub const fn apb2en(&self) -> &Apb2en {
        &self.apb2en
    }
    #[doc = "0x1c - APB1 clock enable register (RCU_APB1EN)"]
    #[inline(always)]
    pub const fn apb1en(&self) -> &Apb1en {
        &self.apb1en
    }
    #[doc = "0x20 - Backup domain control register (RCU_BDCTL)"]
    #[inline(always)]
    pub const fn bdctl(&self) -> &Bdctl {
        &self.bdctl
    }
    #[doc = "0x24 - Reset source /clock register (RCU_RSTSCK)"]
    #[inline(always)]
    pub const fn rstsck(&self) -> &Rstsck {
        &self.rstsck
    }
    #[doc = "0x28 - AHB reset register"]
    #[inline(always)]
    pub const fn ahbrst(&self) -> &Ahbrst {
        &self.ahbrst
    }
    #[doc = "0x2c - Clock Configuration register 1"]
    #[inline(always)]
    pub const fn cfg1(&self) -> &Cfg1 {
        &self.cfg1
    }
    #[doc = "0x34 - Deep sleep mode Voltage register"]
    #[inline(always)]
    pub const fn dsv(&self) -> &Dsv {
        &self.dsv
    }
    #[doc = "0xc0 - Additional clock control register"]
    #[inline(always)]
    pub const fn addctl(&self) -> &Addctl {
        &self.addctl
    }
    #[doc = "0xc4 - Additional clock configuration register"]
    #[inline(always)]
    pub const fn addcfg(&self) -> &Addcfg {
        &self.addcfg
    }
    #[doc = "0xcc - Additional clock interrupt register"]
    #[inline(always)]
    pub const fn addint(&self) -> &Addint {
        &self.addint
    }
    #[doc = "0xd0 - PLL clock spread spectrum control register"]
    #[inline(always)]
    pub const fn pllssctl(&self) -> &Pllssctl {
        &self.pllssctl
    }
    #[doc = "0xd4 - Clock configuration register 2"]
    #[inline(always)]
    pub const fn cfg2(&self) -> &Cfg2 {
        &self.cfg2
    }
    #[doc = "0xe0 - APB1 additional reset register"]
    #[inline(always)]
    pub const fn addapb1rst(&self) -> &Addapb1rst {
        &self.addapb1rst
    }
    #[doc = "0xe4 - APB1 additional enable register"]
    #[inline(always)]
    pub const fn addapb1en(&self) -> &Addapb1en {
        &self.addapb1en
    }
}
#[doc = "CTL (rw) register accessor: Control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl`]
module"]
#[doc(alias = "CTL")]
pub type Ctl = crate::Reg<ctl::CtlSpec>;
#[doc = "Control register"]
pub mod ctl;
#[doc = "CFG0 (rw) register accessor: Clock configuration register 0 (RCU_CFG0)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cfg0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cfg0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cfg0`]
module"]
#[doc(alias = "CFG0")]
pub type Cfg0 = crate::Reg<cfg0::Cfg0Spec>;
#[doc = "Clock configuration register 0 (RCU_CFG0)"]
pub mod cfg0;
#[doc = "INT (rw) register accessor: Clock interrupt register (RCU_INT)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`int::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`int::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int`]
module"]
#[doc(alias = "INT")]
pub type Int = crate::Reg<int::IntSpec>;
#[doc = "Clock interrupt register (RCU_INT)"]
pub mod int;
#[doc = "APB2RST (rw) register accessor: APB2 reset register (RCU_APB2RST)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`apb2rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`apb2rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@apb2rst`]
module"]
#[doc(alias = "APB2RST")]
pub type Apb2rst = crate::Reg<apb2rst::Apb2rstSpec>;
#[doc = "APB2 reset register (RCU_APB2RST)"]
pub mod apb2rst;
#[doc = "APB1RST (rw) register accessor: APB1 reset register (RCU_APB1RST)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`apb1rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`apb1rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@apb1rst`]
module"]
#[doc(alias = "APB1RST")]
pub type Apb1rst = crate::Reg<apb1rst::Apb1rstSpec>;
#[doc = "APB1 reset register (RCU_APB1RST)"]
pub mod apb1rst;
#[doc = "AHBEN (rw) register accessor: AHB enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ahben::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ahben::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ahben`]
module"]
#[doc(alias = "AHBEN")]
pub type Ahben = crate::Reg<ahben::AhbenSpec>;
#[doc = "AHB enable register"]
pub mod ahben;
#[doc = "APB2EN (rw) register accessor: APB2 clock enable register (RCU_APB2EN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`apb2en::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`apb2en::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@apb2en`]
module"]
#[doc(alias = "APB2EN")]
pub type Apb2en = crate::Reg<apb2en::Apb2enSpec>;
#[doc = "APB2 clock enable register (RCU_APB2EN)"]
pub mod apb2en;
#[doc = "APB1EN (rw) register accessor: APB1 clock enable register (RCU_APB1EN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`apb1en::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`apb1en::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@apb1en`]
module"]
#[doc(alias = "APB1EN")]
pub type Apb1en = crate::Reg<apb1en::Apb1enSpec>;
#[doc = "APB1 clock enable register (RCU_APB1EN)"]
pub mod apb1en;
#[doc = "BDCTL (rw) register accessor: Backup domain control register (RCU_BDCTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`bdctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bdctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bdctl`]
module"]
#[doc(alias = "BDCTL")]
pub type Bdctl = crate::Reg<bdctl::BdctlSpec>;
#[doc = "Backup domain control register (RCU_BDCTL)"]
pub mod bdctl;
#[doc = "RSTSCK (rw) register accessor: Reset source /clock register (RCU_RSTSCK)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rstsck::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rstsck::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rstsck`]
module"]
#[doc(alias = "RSTSCK")]
pub type Rstsck = crate::Reg<rstsck::RstsckSpec>;
#[doc = "Reset source /clock register (RCU_RSTSCK)"]
pub mod rstsck;
#[doc = "AHBRST (rw) register accessor: AHB reset register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ahbrst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ahbrst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ahbrst`]
module"]
#[doc(alias = "AHBRST")]
pub type Ahbrst = crate::Reg<ahbrst::AhbrstSpec>;
#[doc = "AHB reset register"]
pub mod ahbrst;
#[doc = "CFG1 (rw) register accessor: Clock Configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cfg1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cfg1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cfg1`]
module"]
#[doc(alias = "CFG1")]
pub type Cfg1 = crate::Reg<cfg1::Cfg1Spec>;
#[doc = "Clock Configuration register 1"]
pub mod cfg1;
#[doc = "DSV (rw) register accessor: Deep sleep mode Voltage register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dsv::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dsv::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dsv`]
module"]
#[doc(alias = "DSV")]
pub type Dsv = crate::Reg<dsv::DsvSpec>;
#[doc = "Deep sleep mode Voltage register"]
pub mod dsv;
#[doc = "ADDCTL (rw) register accessor: Additional clock control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`addctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`addctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@addctl`]
module"]
#[doc(alias = "ADDCTL")]
pub type Addctl = crate::Reg<addctl::AddctlSpec>;
#[doc = "Additional clock control register"]
pub mod addctl;
#[doc = "ADDCFG (rw) register accessor: Additional clock configuration register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`addcfg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`addcfg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@addcfg`]
module"]
#[doc(alias = "ADDCFG")]
pub type Addcfg = crate::Reg<addcfg::AddcfgSpec>;
#[doc = "Additional clock configuration register"]
pub mod addcfg;
#[doc = "ADDINT (rw) register accessor: Additional clock interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`addint::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`addint::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@addint`]
module"]
#[doc(alias = "ADDINT")]
pub type Addint = crate::Reg<addint::AddintSpec>;
#[doc = "Additional clock interrupt register"]
pub mod addint;
#[doc = "PLLSSCTL (rw) register accessor: PLL clock spread spectrum control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pllssctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pllssctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pllssctl`]
module"]
#[doc(alias = "PLLSSCTL")]
pub type Pllssctl = crate::Reg<pllssctl::PllssctlSpec>;
#[doc = "PLL clock spread spectrum control register"]
pub mod pllssctl;
#[doc = "CFG2 (rw) register accessor: Clock configuration register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cfg2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cfg2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cfg2`]
module"]
#[doc(alias = "CFG2")]
pub type Cfg2 = crate::Reg<cfg2::Cfg2Spec>;
#[doc = "Clock configuration register 2"]
pub mod cfg2;
#[doc = "ADDAPB1RST (rw) register accessor: APB1 additional reset register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`addapb1rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`addapb1rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@addapb1rst`]
module"]
#[doc(alias = "ADDAPB1RST")]
pub type Addapb1rst = crate::Reg<addapb1rst::Addapb1rstSpec>;
#[doc = "APB1 additional reset register"]
pub mod addapb1rst;
#[doc = "ADDAPB1EN (rw) register accessor: APB1 additional enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`addapb1en::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`addapb1en::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@addapb1en`]
module"]
#[doc(alias = "ADDAPB1EN")]
pub type Addapb1en = crate::Reg<addapb1en::Addapb1enSpec>;
#[doc = "APB1 additional enable register"]
pub mod addapb1en;
