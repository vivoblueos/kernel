#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    ctl0: Ctl0,
    cs0: Cs0,
    ctl1: Ctl1,
    cs1: Cs1,
}
impl RegisterBlock {
    #[doc = "0x00 - power control register 0"]
    #[inline(always)]
    pub const fn ctl0(&self) -> &Ctl0 {
        &self.ctl0
    }
    #[doc = "0x04 - power control/status register 0"]
    #[inline(always)]
    pub const fn cs0(&self) -> &Cs0 {
        &self.cs0
    }
    #[doc = "0x08 - power control register 1"]
    #[inline(always)]
    pub const fn ctl1(&self) -> &Ctl1 {
        &self.ctl1
    }
    #[doc = "0x0c - power control and status register 1"]
    #[inline(always)]
    pub const fn cs1(&self) -> &Cs1 {
        &self.cs1
    }
}
#[doc = "CTL0 (rw) register accessor: power control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl0`]
module"]
#[doc(alias = "CTL0")]
pub type Ctl0 = crate::Reg<ctl0::Ctl0Spec>;
#[doc = "power control register 0"]
pub mod ctl0;
#[doc = "CS0 (rw) register accessor: power control/status register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cs0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cs0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cs0`]
module"]
#[doc(alias = "CS0")]
pub type Cs0 = crate::Reg<cs0::Cs0Spec>;
#[doc = "power control/status register 0"]
pub mod cs0;
#[doc = "CTL1 (rw) register accessor: power control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl1`]
module"]
#[doc(alias = "CTL1")]
pub type Ctl1 = crate::Reg<ctl1::Ctl1Spec>;
#[doc = "power control register 1"]
pub mod ctl1;
#[doc = "CS1 (rw) register accessor: power control and status register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cs1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cs1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cs1`]
module"]
#[doc(alias = "CS1")]
pub type Cs1 = crate::Reg<cs1::Cs1Spec>;
#[doc = "power control and status register 1"]
pub mod cs1;
