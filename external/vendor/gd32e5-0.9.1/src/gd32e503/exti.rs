#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    inten: Inten,
    even: Even,
    rten: Rten,
    ften: Ften,
    swiev: Swiev,
    pd: Pd,
}
impl RegisterBlock {
    #[doc = "0x00 - Interrupt enable register (EXTI_INTEN)"]
    #[inline(always)]
    pub const fn inten(&self) -> &Inten {
        &self.inten
    }
    #[doc = "0x04 - Event enable register (EXTI_EVEN)"]
    #[inline(always)]
    pub const fn even(&self) -> &Even {
        &self.even
    }
    #[doc = "0x08 - Rising Edge Trigger Enable register (EXTI_RTEN)"]
    #[inline(always)]
    pub const fn rten(&self) -> &Rten {
        &self.rten
    }
    #[doc = "0x0c - Falling Egde Trigger Enable register (EXTI_FTEN)"]
    #[inline(always)]
    pub const fn ften(&self) -> &Ften {
        &self.ften
    }
    #[doc = "0x10 - Software interrupt event register (EXTI_SWIEV)"]
    #[inline(always)]
    pub const fn swiev(&self) -> &Swiev {
        &self.swiev
    }
    #[doc = "0x14 - Pending register (EXTI_PD)"]
    #[inline(always)]
    pub const fn pd(&self) -> &Pd {
        &self.pd
    }
}
#[doc = "INTEN (rw) register accessor: Interrupt enable register (EXTI_INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@inten`]
module"]
#[doc(alias = "INTEN")]
pub type Inten = crate::Reg<inten::IntenSpec>;
#[doc = "Interrupt enable register (EXTI_INTEN)"]
pub mod inten;
#[doc = "EVEN (rw) register accessor: Event enable register (EXTI_EVEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`even::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`even::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@even`]
module"]
#[doc(alias = "EVEN")]
pub type Even = crate::Reg<even::EvenSpec>;
#[doc = "Event enable register (EXTI_EVEN)"]
pub mod even;
#[doc = "RTEN (rw) register accessor: Rising Edge Trigger Enable register (EXTI_RTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rten`]
module"]
#[doc(alias = "RTEN")]
pub type Rten = crate::Reg<rten::RtenSpec>;
#[doc = "Rising Edge Trigger Enable register (EXTI_RTEN)"]
pub mod rten;
#[doc = "FTEN (rw) register accessor: Falling Egde Trigger Enable register (EXTI_FTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ften::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ften::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ften`]
module"]
#[doc(alias = "FTEN")]
pub type Ften = crate::Reg<ften::FtenSpec>;
#[doc = "Falling Egde Trigger Enable register (EXTI_FTEN)"]
pub mod ften;
#[doc = "SWIEV (rw) register accessor: Software interrupt event register (EXTI_SWIEV)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`swiev::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`swiev::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@swiev`]
module"]
#[doc(alias = "SWIEV")]
pub type Swiev = crate::Reg<swiev::SwievSpec>;
#[doc = "Software interrupt event register (EXTI_SWIEV)"]
pub mod swiev;
#[doc = "PD (rw) register accessor: Pending register (EXTI_PD)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pd::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pd::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pd`]
module"]
#[doc(alias = "PD")]
pub type Pd = crate::Reg<pd::PdSpec>;
#[doc = "Pending register (EXTI_PD)"]
pub mod pd;
