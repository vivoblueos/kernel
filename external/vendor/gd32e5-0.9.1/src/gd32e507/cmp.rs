#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    _reserved0: [u8; 0x20],
    cmp1_cs: Cmp1Cs,
    _reserved1: [u8; 0x04],
    cmp3_cs: Cmp3Cs,
    _reserved2: [u8; 0x04],
    cmp5_cs: Cmp5Cs,
}
impl RegisterBlock {
    #[doc = "0x20 - CMP1 control and status register"]
    #[inline(always)]
    pub const fn cmp1_cs(&self) -> &Cmp1Cs {
        &self.cmp1_cs
    }
    #[doc = "0x28 - CMP3 control and status register"]
    #[inline(always)]
    pub const fn cmp3_cs(&self) -> &Cmp3Cs {
        &self.cmp3_cs
    }
    #[doc = "0x30 - CMP5 control and status register"]
    #[inline(always)]
    pub const fn cmp5_cs(&self) -> &Cmp5Cs {
        &self.cmp5_cs
    }
}
#[doc = "CMP1_CS (rw) register accessor: CMP1 control and status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cmp1_cs::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cmp1_cs::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cmp1_cs`]
module"]
#[doc(alias = "CMP1_CS")]
pub type Cmp1Cs = crate::Reg<cmp1_cs::Cmp1CsSpec>;
#[doc = "CMP1 control and status register"]
pub mod cmp1_cs;
#[doc = "CMP3_CS (rw) register accessor: CMP3 control and status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cmp3_cs::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cmp3_cs::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cmp3_cs`]
module"]
#[doc(alias = "CMP3_CS")]
pub type Cmp3Cs = crate::Reg<cmp3_cs::Cmp3CsSpec>;
#[doc = "CMP3 control and status register"]
pub mod cmp3_cs;
#[doc = "CMP5_CS (rw) register accessor: CMP5 control and status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cmp5_cs::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cmp5_cs::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cmp5_cs`]
module"]
#[doc(alias = "CMP5_CS")]
pub type Cmp5Cs = crate::Reg<cmp5_cs::Cmp5CsSpec>;
#[doc = "CMP5 control and status register"]
pub mod cmp5_cs;
