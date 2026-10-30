#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    ctl0: Ctl0,
    ctl1: Ctl1,
    intf: Intf,
    intc: Intc,
    inten: Inten,
    chouten: Chouten,
    choutdis: Choutdis,
    choutdisf: Choutdisf,
    bmctl: Bmctl,
    bmstrg: Bmstrg,
    bmcmpv: Bmcmpv,
    bmcar: Bmcar,
    exevcfg0: Exevcfg0,
    exevcfg1: Exevcfg1,
    exevdfctl: Exevdfctl,
    adctrigs0: Adctrigs0,
    adctrigs1: Adctrigs1,
    adctrigs2: Adctrigs2,
    adctrigs3: Adctrigs3,
    dllcctl: Dllcctl,
    fltincfg0: Fltincfg0,
    fltincfg1: Fltincfg1,
    dmaupmtr: Dmaupmtr,
    dmaupst0r: Dmaupst0r,
    dmaupst1r: Dmaupst1r,
    dmaupst2r: Dmaupst2r,
    dmaupst3r: Dmaupst3r,
    dmaupst4r: Dmaupst4r,
    dmatb: Dmatb,
}
impl RegisterBlock {
    #[doc = "0x00 - SHRTIMER control register 0"]
    #[inline(always)]
    pub const fn ctl0(&self) -> &Ctl0 {
        &self.ctl0
    }
    #[doc = "0x04 - SHRTIMER control register 1"]
    #[inline(always)]
    pub const fn ctl1(&self) -> &Ctl1 {
        &self.ctl1
    }
    #[doc = "0x08 - SHRTIMER interrupt flag register"]
    #[inline(always)]
    pub const fn intf(&self) -> &Intf {
        &self.intf
    }
    #[doc = "0x0c - SHRTIMER interrupt flag clear register"]
    #[inline(always)]
    pub const fn intc(&self) -> &Intc {
        &self.intc
    }
    #[doc = "0x10 - SHRTIMER interrupt enable register"]
    #[inline(always)]
    pub const fn inten(&self) -> &Inten {
        &self.inten
    }
    #[doc = "0x14 - SHRTIMER channel output enable register"]
    #[inline(always)]
    pub const fn chouten(&self) -> &Chouten {
        &self.chouten
    }
    #[doc = "0x18 - SHRTIMER channel output disable register"]
    #[inline(always)]
    pub const fn choutdis(&self) -> &Choutdis {
        &self.choutdis
    }
    #[doc = "0x1c - SHRTIMER channel output disable flag register"]
    #[inline(always)]
    pub const fn choutdisf(&self) -> &Choutdisf {
        &self.choutdisf
    }
    #[doc = "0x20 - SHRTIMER bunch mode control register"]
    #[inline(always)]
    pub const fn bmctl(&self) -> &Bmctl {
        &self.bmctl
    }
    #[doc = "0x24 - SHRTIMER bunch mode start trigger register"]
    #[inline(always)]
    pub const fn bmstrg(&self) -> &Bmstrg {
        &self.bmstrg
    }
    #[doc = "0x28 - SHRTIMER bunch mode compare value register"]
    #[inline(always)]
    pub const fn bmcmpv(&self) -> &Bmcmpv {
        &self.bmcmpv
    }
    #[doc = "0x2c - SHRTIMER bunch mode counter auto reload register"]
    #[inline(always)]
    pub const fn bmcar(&self) -> &Bmcar {
        &self.bmcar
    }
    #[doc = "0x30 - SHRTIMER external event configuration register 0"]
    #[inline(always)]
    pub const fn exevcfg0(&self) -> &Exevcfg0 {
        &self.exevcfg0
    }
    #[doc = "0x34 - SHRTIMER external event configuration register 1"]
    #[inline(always)]
    pub const fn exevcfg1(&self) -> &Exevcfg1 {
        &self.exevcfg1
    }
    #[doc = "0x38 - SHRTIMER external event digital filter control register"]
    #[inline(always)]
    pub const fn exevdfctl(&self) -> &Exevdfctl {
        &self.exevdfctl
    }
    #[doc = "0x3c - SHRTIMER trigger source 0 to ADC register"]
    #[inline(always)]
    pub const fn adctrigs0(&self) -> &Adctrigs0 {
        &self.adctrigs0
    }
    #[doc = "0x40 - SHRTIMER trigger source 1 to ADC register"]
    #[inline(always)]
    pub const fn adctrigs1(&self) -> &Adctrigs1 {
        &self.adctrigs1
    }
    #[doc = "0x44 - SHRTIMER trigger source 2 to ADC register"]
    #[inline(always)]
    pub const fn adctrigs2(&self) -> &Adctrigs2 {
        &self.adctrigs2
    }
    #[doc = "0x48 - SHRTIMER trigger source 3 to ADC register"]
    #[inline(always)]
    pub const fn adctrigs3(&self) -> &Adctrigs3 {
        &self.adctrigs3
    }
    #[doc = "0x4c - SHRTIMER DLL calibration control register"]
    #[inline(always)]
    pub const fn dllcctl(&self) -> &Dllcctl {
        &self.dllcctl
    }
    #[doc = "0x50 - SHRTIMER fault input configuration register 0"]
    #[inline(always)]
    pub const fn fltincfg0(&self) -> &Fltincfg0 {
        &self.fltincfg0
    }
    #[doc = "0x54 - SHRTIMER fault input configuration register 1"]
    #[inline(always)]
    pub const fn fltincfg1(&self) -> &Fltincfg1 {
        &self.fltincfg1
    }
    #[doc = "0x58 - SHRTIMER DMA update Master_TIMER register"]
    #[inline(always)]
    pub const fn dmaupmtr(&self) -> &Dmaupmtr {
        &self.dmaupmtr
    }
    #[doc = "0x5c - SHRTIMER DMA update Slave_TIMER0 register"]
    #[inline(always)]
    pub const fn dmaupst0r(&self) -> &Dmaupst0r {
        &self.dmaupst0r
    }
    #[doc = "0x60 - SHRTIMER DMA update Slave_TIMER1 register"]
    #[inline(always)]
    pub const fn dmaupst1r(&self) -> &Dmaupst1r {
        &self.dmaupst1r
    }
    #[doc = "0x64 - SHRTIMER DMA update Slave_TIMER2 register"]
    #[inline(always)]
    pub const fn dmaupst2r(&self) -> &Dmaupst2r {
        &self.dmaupst2r
    }
    #[doc = "0x68 - SHRTIMER DMA update Slave_TIMER3 register"]
    #[inline(always)]
    pub const fn dmaupst3r(&self) -> &Dmaupst3r {
        &self.dmaupst3r
    }
    #[doc = "0x6c - SHRTIMER DMA update Slave_TIMER4 register"]
    #[inline(always)]
    pub const fn dmaupst4r(&self) -> &Dmaupst4r {
        &self.dmaupst4r
    }
    #[doc = "0x70 - SHRTIMER DMA transfer buffer register"]
    #[inline(always)]
    pub const fn dmatb(&self) -> &Dmatb {
        &self.dmatb
    }
}
#[doc = "CTL0 (rw) register accessor: SHRTIMER control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl0`]
module"]
#[doc(alias = "CTL0")]
pub type Ctl0 = crate::Reg<ctl0::Ctl0Spec>;
#[doc = "SHRTIMER control register 0"]
pub mod ctl0;
#[doc = "CTL1 (rw) register accessor: SHRTIMER control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl1`]
module"]
#[doc(alias = "CTL1")]
pub type Ctl1 = crate::Reg<ctl1::Ctl1Spec>;
#[doc = "SHRTIMER control register 1"]
pub mod ctl1;
#[doc = "INTF (r) register accessor: SHRTIMER interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`intf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@intf`]
module"]
#[doc(alias = "INTF")]
pub type Intf = crate::Reg<intf::IntfSpec>;
#[doc = "SHRTIMER interrupt flag register"]
pub mod intf;
#[doc = "INTC (w) register accessor: SHRTIMER interrupt flag clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`intc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@intc`]
module"]
#[doc(alias = "INTC")]
pub type Intc = crate::Reg<intc::IntcSpec>;
#[doc = "SHRTIMER interrupt flag clear register"]
pub mod intc;
#[doc = "INTEN (rw) register accessor: SHRTIMER interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@inten`]
module"]
#[doc(alias = "INTEN")]
pub type Inten = crate::Reg<inten::IntenSpec>;
#[doc = "SHRTIMER interrupt enable register"]
pub mod inten;
#[doc = "CHOUTEN (rw) register accessor: SHRTIMER channel output enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chouten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chouten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@chouten`]
module"]
#[doc(alias = "CHOUTEN")]
pub type Chouten = crate::Reg<chouten::ChoutenSpec>;
#[doc = "SHRTIMER channel output enable register"]
pub mod chouten;
#[doc = "CHOUTDIS (w) register accessor: SHRTIMER channel output disable register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`choutdis::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@choutdis`]
module"]
#[doc(alias = "CHOUTDIS")]
pub type Choutdis = crate::Reg<choutdis::ChoutdisSpec>;
#[doc = "SHRTIMER channel output disable register"]
pub mod choutdis;
#[doc = "CHOUTDISF (r) register accessor: SHRTIMER channel output disable flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`choutdisf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@choutdisf`]
module"]
#[doc(alias = "CHOUTDISF")]
pub type Choutdisf = crate::Reg<choutdisf::ChoutdisfSpec>;
#[doc = "SHRTIMER channel output disable flag register"]
pub mod choutdisf;
#[doc = "BMCTL (rw) register accessor: SHRTIMER bunch mode control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`bmctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bmctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bmctl`]
module"]
#[doc(alias = "BMCTL")]
pub type Bmctl = crate::Reg<bmctl::BmctlSpec>;
#[doc = "SHRTIMER bunch mode control register"]
pub mod bmctl;
#[doc = "BMSTRG (rw) register accessor: SHRTIMER bunch mode start trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`bmstrg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bmstrg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bmstrg`]
module"]
#[doc(alias = "BMSTRG")]
pub type Bmstrg = crate::Reg<bmstrg::BmstrgSpec>;
#[doc = "SHRTIMER bunch mode start trigger register"]
pub mod bmstrg;
#[doc = "BMCMPV (rw) register accessor: SHRTIMER bunch mode compare value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`bmcmpv::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bmcmpv::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bmcmpv`]
module"]
#[doc(alias = "BMCMPV")]
pub type Bmcmpv = crate::Reg<bmcmpv::BmcmpvSpec>;
#[doc = "SHRTIMER bunch mode compare value register"]
pub mod bmcmpv;
#[doc = "BMCAR (rw) register accessor: SHRTIMER bunch mode counter auto reload register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`bmcar::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bmcar::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bmcar`]
module"]
#[doc(alias = "BMCAR")]
pub type Bmcar = crate::Reg<bmcar::BmcarSpec>;
#[doc = "SHRTIMER bunch mode counter auto reload register"]
pub mod bmcar;
#[doc = "EXEVCFG0 (rw) register accessor: SHRTIMER external event configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`exevcfg0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`exevcfg0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@exevcfg0`]
module"]
#[doc(alias = "EXEVCFG0")]
pub type Exevcfg0 = crate::Reg<exevcfg0::Exevcfg0Spec>;
#[doc = "SHRTIMER external event configuration register 0"]
pub mod exevcfg0;
#[doc = "EXEVCFG1 (rw) register accessor: SHRTIMER external event configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`exevcfg1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`exevcfg1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@exevcfg1`]
module"]
#[doc(alias = "EXEVCFG1")]
pub type Exevcfg1 = crate::Reg<exevcfg1::Exevcfg1Spec>;
#[doc = "SHRTIMER external event configuration register 1"]
pub mod exevcfg1;
#[doc = "EXEVDFCTL (rw) register accessor: SHRTIMER external event digital filter control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`exevdfctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`exevdfctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@exevdfctl`]
module"]
#[doc(alias = "EXEVDFCTL")]
pub type Exevdfctl = crate::Reg<exevdfctl::ExevdfctlSpec>;
#[doc = "SHRTIMER external event digital filter control register"]
pub mod exevdfctl;
#[doc = "ADCTRIGS0 (rw) register accessor: SHRTIMER trigger source 0 to ADC register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`adctrigs0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`adctrigs0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@adctrigs0`]
module"]
#[doc(alias = "ADCTRIGS0")]
pub type Adctrigs0 = crate::Reg<adctrigs0::Adctrigs0Spec>;
#[doc = "SHRTIMER trigger source 0 to ADC register"]
pub mod adctrigs0;
#[doc = "ADCTRIGS1 (rw) register accessor: SHRTIMER trigger source 1 to ADC register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`adctrigs1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`adctrigs1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@adctrigs1`]
module"]
#[doc(alias = "ADCTRIGS1")]
pub type Adctrigs1 = crate::Reg<adctrigs1::Adctrigs1Spec>;
#[doc = "SHRTIMER trigger source 1 to ADC register"]
pub mod adctrigs1;
#[doc = "ADCTRIGS2 (rw) register accessor: SHRTIMER trigger source 2 to ADC register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`adctrigs2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`adctrigs2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@adctrigs2`]
module"]
#[doc(alias = "ADCTRIGS2")]
pub type Adctrigs2 = crate::Reg<adctrigs2::Adctrigs2Spec>;
#[doc = "SHRTIMER trigger source 2 to ADC register"]
pub mod adctrigs2;
#[doc = "ADCTRIGS3 (rw) register accessor: SHRTIMER trigger source 3 to ADC register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`adctrigs3::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`adctrigs3::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@adctrigs3`]
module"]
#[doc(alias = "ADCTRIGS3")]
pub type Adctrigs3 = crate::Reg<adctrigs3::Adctrigs3Spec>;
#[doc = "SHRTIMER trigger source 3 to ADC register"]
pub mod adctrigs3;
#[doc = "DLLCCTL (rw) register accessor: SHRTIMER DLL calibration control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dllcctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dllcctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dllcctl`]
module"]
#[doc(alias = "DLLCCTL")]
pub type Dllcctl = crate::Reg<dllcctl::DllcctlSpec>;
#[doc = "SHRTIMER DLL calibration control register"]
pub mod dllcctl;
#[doc = "FLTINCFG0 (rw) register accessor: SHRTIMER fault input configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fltincfg0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fltincfg0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fltincfg0`]
module"]
#[doc(alias = "FLTINCFG0")]
pub type Fltincfg0 = crate::Reg<fltincfg0::Fltincfg0Spec>;
#[doc = "SHRTIMER fault input configuration register 0"]
pub mod fltincfg0;
#[doc = "FLTINCFG1 (rw) register accessor: SHRTIMER fault input configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fltincfg1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fltincfg1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fltincfg1`]
module"]
#[doc(alias = "FLTINCFG1")]
pub type Fltincfg1 = crate::Reg<fltincfg1::Fltincfg1Spec>;
#[doc = "SHRTIMER fault input configuration register 1"]
pub mod fltincfg1;
#[doc = "DMAUPMTR (rw) register accessor: SHRTIMER DMA update Master_TIMER register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmaupmtr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmaupmtr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dmaupmtr`]
module"]
#[doc(alias = "DMAUPMTR")]
pub type Dmaupmtr = crate::Reg<dmaupmtr::DmaupmtrSpec>;
#[doc = "SHRTIMER DMA update Master_TIMER register"]
pub mod dmaupmtr;
#[doc = "DMAUPST0R (rw) register accessor: SHRTIMER DMA update Slave_TIMER0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmaupst0r::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmaupst0r::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dmaupst0r`]
module"]
#[doc(alias = "DMAUPST0R")]
pub type Dmaupst0r = crate::Reg<dmaupst0r::Dmaupst0rSpec>;
#[doc = "SHRTIMER DMA update Slave_TIMER0 register"]
pub mod dmaupst0r;
#[doc = "DMAUPST1R (rw) register accessor: SHRTIMER DMA update Slave_TIMER1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmaupst1r::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmaupst1r::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dmaupst1r`]
module"]
#[doc(alias = "DMAUPST1R")]
pub type Dmaupst1r = crate::Reg<dmaupst1r::Dmaupst1rSpec>;
#[doc = "SHRTIMER DMA update Slave_TIMER1 register"]
pub mod dmaupst1r;
#[doc = "DMAUPST2R (rw) register accessor: SHRTIMER DMA update Slave_TIMER2 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmaupst2r::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmaupst2r::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dmaupst2r`]
module"]
#[doc(alias = "DMAUPST2R")]
pub type Dmaupst2r = crate::Reg<dmaupst2r::Dmaupst2rSpec>;
#[doc = "SHRTIMER DMA update Slave_TIMER2 register"]
pub mod dmaupst2r;
#[doc = "DMAUPST3R (rw) register accessor: SHRTIMER DMA update Slave_TIMER3 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmaupst3r::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmaupst3r::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dmaupst3r`]
module"]
#[doc(alias = "DMAUPST3R")]
pub type Dmaupst3r = crate::Reg<dmaupst3r::Dmaupst3rSpec>;
#[doc = "SHRTIMER DMA update Slave_TIMER3 register"]
pub mod dmaupst3r;
#[doc = "DMAUPST4R (rw) register accessor: SHRTIMER DMA update Slave_TIMER4 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmaupst4r::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmaupst4r::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dmaupst4r`]
module"]
#[doc(alias = "DMAUPST4R")]
pub type Dmaupst4r = crate::Reg<dmaupst4r::Dmaupst4rSpec>;
#[doc = "SHRTIMER DMA update Slave_TIMER4 register"]
pub mod dmaupst4r;
#[doc = "DMATB (w) register accessor: SHRTIMER DMA transfer buffer register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmatb::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dmatb`]
module"]
#[doc(alias = "DMATB")]
pub type Dmatb = crate::Reg<dmatb::DmatbSpec>;
#[doc = "SHRTIMER DMA transfer buffer register"]
pub mod dmatb;
