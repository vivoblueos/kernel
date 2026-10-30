#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    snctl0: Snctl0,
    sntcfg0: Sntcfg0,
    snctl1: Snctl1,
    sntcfg1: Sntcfg1,
    snctl2: Snctl2,
    sntcfg2: Sntcfg2,
    snctl3: Snctl3,
    sntcfg3: Sntcfg3,
    _reserved8: [u8; 0x40],
    npctl1: Npctl1,
    npinten1: Npinten1,
    npctcfg1: Npctcfg1,
    npatcfg1: Npatcfg1,
    _reserved12: [u8; 0x04],
    necc1: Necc1,
    _reserved13: [u8; 0x08],
    npctl2: Npctl2,
    npinten2: Npinten2,
    npctcfg2: Npctcfg2,
    npatcfg2: Npatcfg2,
    _reserved17: [u8; 0x04],
    necc2: Necc2,
    _reserved18: [u8; 0x08],
    npctl3: Npctl3,
    npinten3: Npinten3,
    npctcfg3: Npctcfg3,
    npatcfg3: Npatcfg3,
    piotcfg3: Piotcfg3,
    _reserved23: [u8; 0x50],
    snwtcfg0: Snwtcfg0,
    _reserved24: [u8; 0x04],
    snwtcfg1: Snwtcfg1,
    _reserved25: [u8; 0x04],
    snwtcfg2: Snwtcfg2,
    _reserved26: [u8; 0x04],
    snwtcfg3: Snwtcfg3,
}
impl RegisterBlock {
    #[doc = "0x00 - SRAM/NOR flash control register 0"]
    #[inline(always)]
    pub const fn snctl0(&self) -> &Snctl0 {
        &self.snctl0
    }
    #[doc = "0x04 - SRAM/NOR flash timing configuration register 0"]
    #[inline(always)]
    pub const fn sntcfg0(&self) -> &Sntcfg0 {
        &self.sntcfg0
    }
    #[doc = "0x08 - SRAM/NOR flash control register 1"]
    #[inline(always)]
    pub const fn snctl1(&self) -> &Snctl1 {
        &self.snctl1
    }
    #[doc = "0x0c - SRAM/NOR flash timing configuration register 1"]
    #[inline(always)]
    pub const fn sntcfg1(&self) -> &Sntcfg1 {
        &self.sntcfg1
    }
    #[doc = "0x10 - SRAM/NOR flash control register 2"]
    #[inline(always)]
    pub const fn snctl2(&self) -> &Snctl2 {
        &self.snctl2
    }
    #[doc = "0x14 - SRAM/NOR flash timing configuration register 2"]
    #[inline(always)]
    pub const fn sntcfg2(&self) -> &Sntcfg2 {
        &self.sntcfg2
    }
    #[doc = "0x18 - SRAM/NOR flash control register 3"]
    #[inline(always)]
    pub const fn snctl3(&self) -> &Snctl3 {
        &self.snctl3
    }
    #[doc = "0x1c - SRAM/NOR flash timing configuration register 3"]
    #[inline(always)]
    pub const fn sntcfg3(&self) -> &Sntcfg3 {
        &self.sntcfg3
    }
    #[doc = "0x60 - NAND flash/PC card control register 1"]
    #[inline(always)]
    pub const fn npctl1(&self) -> &Npctl1 {
        &self.npctl1
    }
    #[doc = "0x64 - NAND flash/PC card interrupt enable register 1"]
    #[inline(always)]
    pub const fn npinten1(&self) -> &Npinten1 {
        &self.npinten1
    }
    #[doc = "0x68 - NAND flash/PC card common space timing configuration register 1"]
    #[inline(always)]
    pub const fn npctcfg1(&self) -> &Npctcfg1 {
        &self.npctcfg1
    }
    #[doc = "0x6c - NAND flash/PC card attribute space timing configuration register 1"]
    #[inline(always)]
    pub const fn npatcfg1(&self) -> &Npatcfg1 {
        &self.npatcfg1
    }
    #[doc = "0x74 - NAND flash ECC register 1"]
    #[inline(always)]
    pub const fn necc1(&self) -> &Necc1 {
        &self.necc1
    }
    #[doc = "0x80 - NAND flash/PC card control register 2"]
    #[inline(always)]
    pub const fn npctl2(&self) -> &Npctl2 {
        &self.npctl2
    }
    #[doc = "0x84 - NAND flash/PC card interrupt enable register 2"]
    #[inline(always)]
    pub const fn npinten2(&self) -> &Npinten2 {
        &self.npinten2
    }
    #[doc = "0x88 - NAND flash/PC card common space timing configuration register 2"]
    #[inline(always)]
    pub const fn npctcfg2(&self) -> &Npctcfg2 {
        &self.npctcfg2
    }
    #[doc = "0x8c - NAND flash/PC card attribute space timing configuration register 2"]
    #[inline(always)]
    pub const fn npatcfg2(&self) -> &Npatcfg2 {
        &self.npatcfg2
    }
    #[doc = "0x94 - NAND flash ECC register 2"]
    #[inline(always)]
    pub const fn necc2(&self) -> &Necc2 {
        &self.necc2
    }
    #[doc = "0xa0 - NAND flash/PC card control register 3"]
    #[inline(always)]
    pub const fn npctl3(&self) -> &Npctl3 {
        &self.npctl3
    }
    #[doc = "0xa4 - NAND flash/PC card interrupt enable register 3"]
    #[inline(always)]
    pub const fn npinten3(&self) -> &Npinten3 {
        &self.npinten3
    }
    #[doc = "0xa8 - NAND flash/PC card common space timing configuration register 3"]
    #[inline(always)]
    pub const fn npctcfg3(&self) -> &Npctcfg3 {
        &self.npctcfg3
    }
    #[doc = "0xac - NAND flash/PC card attribute space timing configuration register 3"]
    #[inline(always)]
    pub const fn npatcfg3(&self) -> &Npatcfg3 {
        &self.npatcfg3
    }
    #[doc = "0xb0 - PC card I/O space timing configuration register"]
    #[inline(always)]
    pub const fn piotcfg3(&self) -> &Piotcfg3 {
        &self.piotcfg3
    }
    #[doc = "0x104 - SRAM/NOR flash write timing configuration register 0"]
    #[inline(always)]
    pub const fn snwtcfg0(&self) -> &Snwtcfg0 {
        &self.snwtcfg0
    }
    #[doc = "0x10c - SRAM/NOR flash write timing configuration register 1"]
    #[inline(always)]
    pub const fn snwtcfg1(&self) -> &Snwtcfg1 {
        &self.snwtcfg1
    }
    #[doc = "0x114 - SRAM/NOR flash write timing configuration register 2"]
    #[inline(always)]
    pub const fn snwtcfg2(&self) -> &Snwtcfg2 {
        &self.snwtcfg2
    }
    #[doc = "0x11c - SRAM/NOR flash write timing configuration register 3"]
    #[inline(always)]
    pub const fn snwtcfg3(&self) -> &Snwtcfg3 {
        &self.snwtcfg3
    }
}
#[doc = "SNCTL0 (rw) register accessor: SRAM/NOR flash control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`snctl0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`snctl0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@snctl0`]
module"]
#[doc(alias = "SNCTL0")]
pub type Snctl0 = crate::Reg<snctl0::Snctl0Spec>;
#[doc = "SRAM/NOR flash control register 0"]
pub mod snctl0;
#[doc = "SNTCFG0 (rw) register accessor: SRAM/NOR flash timing configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`sntcfg0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`sntcfg0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sntcfg0`]
module"]
#[doc(alias = "SNTCFG0")]
pub type Sntcfg0 = crate::Reg<sntcfg0::Sntcfg0Spec>;
#[doc = "SRAM/NOR flash timing configuration register 0"]
pub mod sntcfg0;
#[doc = "SNCTL1 (rw) register accessor: SRAM/NOR flash control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`snctl1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`snctl1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@snctl1`]
module"]
#[doc(alias = "SNCTL1")]
pub type Snctl1 = crate::Reg<snctl1::Snctl1Spec>;
#[doc = "SRAM/NOR flash control register 1"]
pub mod snctl1;
#[doc = "SNTCFG1 (rw) register accessor: SRAM/NOR flash timing configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`sntcfg1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`sntcfg1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sntcfg1`]
module"]
#[doc(alias = "SNTCFG1")]
pub type Sntcfg1 = crate::Reg<sntcfg1::Sntcfg1Spec>;
#[doc = "SRAM/NOR flash timing configuration register 1"]
pub mod sntcfg1;
#[doc = "SNCTL2 (rw) register accessor: SRAM/NOR flash control register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`snctl2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`snctl2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@snctl2`]
module"]
#[doc(alias = "SNCTL2")]
pub type Snctl2 = crate::Reg<snctl2::Snctl2Spec>;
#[doc = "SRAM/NOR flash control register 2"]
pub mod snctl2;
#[doc = "SNTCFG2 (rw) register accessor: SRAM/NOR flash timing configuration register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`sntcfg2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`sntcfg2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sntcfg2`]
module"]
#[doc(alias = "SNTCFG2")]
pub type Sntcfg2 = crate::Reg<sntcfg2::Sntcfg2Spec>;
#[doc = "SRAM/NOR flash timing configuration register 2"]
pub mod sntcfg2;
#[doc = "SNCTL3 (rw) register accessor: SRAM/NOR flash control register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`snctl3::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`snctl3::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@snctl3`]
module"]
#[doc(alias = "SNCTL3")]
pub type Snctl3 = crate::Reg<snctl3::Snctl3Spec>;
#[doc = "SRAM/NOR flash control register 3"]
pub mod snctl3;
#[doc = "SNTCFG3 (rw) register accessor: SRAM/NOR flash timing configuration register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`sntcfg3::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`sntcfg3::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sntcfg3`]
module"]
#[doc(alias = "SNTCFG3")]
pub type Sntcfg3 = crate::Reg<sntcfg3::Sntcfg3Spec>;
#[doc = "SRAM/NOR flash timing configuration register 3"]
pub mod sntcfg3;
#[doc = "SNWTCFG0 (rw) register accessor: SRAM/NOR flash write timing configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`snwtcfg0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`snwtcfg0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@snwtcfg0`]
module"]
#[doc(alias = "SNWTCFG0")]
pub type Snwtcfg0 = crate::Reg<snwtcfg0::Snwtcfg0Spec>;
#[doc = "SRAM/NOR flash write timing configuration register 0"]
pub mod snwtcfg0;
#[doc = "SNWTCFG1 (rw) register accessor: SRAM/NOR flash write timing configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`snwtcfg1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`snwtcfg1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@snwtcfg1`]
module"]
#[doc(alias = "SNWTCFG1")]
pub type Snwtcfg1 = crate::Reg<snwtcfg1::Snwtcfg1Spec>;
#[doc = "SRAM/NOR flash write timing configuration register 1"]
pub mod snwtcfg1;
#[doc = "SNWTCFG2 (rw) register accessor: SRAM/NOR flash write timing configuration register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`snwtcfg2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`snwtcfg2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@snwtcfg2`]
module"]
#[doc(alias = "SNWTCFG2")]
pub type Snwtcfg2 = crate::Reg<snwtcfg2::Snwtcfg2Spec>;
#[doc = "SRAM/NOR flash write timing configuration register 2"]
pub mod snwtcfg2;
#[doc = "SNWTCFG3 (rw) register accessor: SRAM/NOR flash write timing configuration register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`snwtcfg3::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`snwtcfg3::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@snwtcfg3`]
module"]
#[doc(alias = "SNWTCFG3")]
pub type Snwtcfg3 = crate::Reg<snwtcfg3::Snwtcfg3Spec>;
#[doc = "SRAM/NOR flash write timing configuration register 3"]
pub mod snwtcfg3;
#[doc = "NPCTL1 (rw) register accessor: NAND flash/PC card control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npctl1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npctl1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@npctl1`]
module"]
#[doc(alias = "NPCTL1")]
pub type Npctl1 = crate::Reg<npctl1::Npctl1Spec>;
#[doc = "NAND flash/PC card control register 1"]
pub mod npctl1;
#[doc = "NPCTL2 (rw) register accessor: NAND flash/PC card control register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npctl2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npctl2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@npctl2`]
module"]
#[doc(alias = "NPCTL2")]
pub type Npctl2 = crate::Reg<npctl2::Npctl2Spec>;
#[doc = "NAND flash/PC card control register 2"]
pub mod npctl2;
#[doc = "NPCTL3 (rw) register accessor: NAND flash/PC card control register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npctl3::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npctl3::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@npctl3`]
module"]
#[doc(alias = "NPCTL3")]
pub type Npctl3 = crate::Reg<npctl3::Npctl3Spec>;
#[doc = "NAND flash/PC card control register 3"]
pub mod npctl3;
#[doc = "NPINTEN1 (rw) register accessor: NAND flash/PC card interrupt enable register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npinten1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npinten1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@npinten1`]
module"]
#[doc(alias = "NPINTEN1")]
pub type Npinten1 = crate::Reg<npinten1::Npinten1Spec>;
#[doc = "NAND flash/PC card interrupt enable register 1"]
pub mod npinten1;
#[doc = "NPINTEN2 (rw) register accessor: NAND flash/PC card interrupt enable register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npinten2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npinten2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@npinten2`]
module"]
#[doc(alias = "NPINTEN2")]
pub type Npinten2 = crate::Reg<npinten2::Npinten2Spec>;
#[doc = "NAND flash/PC card interrupt enable register 2"]
pub mod npinten2;
#[doc = "NPINTEN3 (rw) register accessor: NAND flash/PC card interrupt enable register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npinten3::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npinten3::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@npinten3`]
module"]
#[doc(alias = "NPINTEN3")]
pub type Npinten3 = crate::Reg<npinten3::Npinten3Spec>;
#[doc = "NAND flash/PC card interrupt enable register 3"]
pub mod npinten3;
#[doc = "NPCTCFG1 (rw) register accessor: NAND flash/PC card common space timing configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npctcfg1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npctcfg1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@npctcfg1`]
module"]
#[doc(alias = "NPCTCFG1")]
pub type Npctcfg1 = crate::Reg<npctcfg1::Npctcfg1Spec>;
#[doc = "NAND flash/PC card common space timing configuration register 1"]
pub mod npctcfg1;
#[doc = "NPCTCFG2 (rw) register accessor: NAND flash/PC card common space timing configuration register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npctcfg2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npctcfg2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@npctcfg2`]
module"]
#[doc(alias = "NPCTCFG2")]
pub type Npctcfg2 = crate::Reg<npctcfg2::Npctcfg2Spec>;
#[doc = "NAND flash/PC card common space timing configuration register 2"]
pub mod npctcfg2;
#[doc = "NPCTCFG3 (rw) register accessor: NAND flash/PC card common space timing configuration register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npctcfg3::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npctcfg3::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@npctcfg3`]
module"]
#[doc(alias = "NPCTCFG3")]
pub type Npctcfg3 = crate::Reg<npctcfg3::Npctcfg3Spec>;
#[doc = "NAND flash/PC card common space timing configuration register 3"]
pub mod npctcfg3;
#[doc = "NPATCFG1 (rw) register accessor: NAND flash/PC card attribute space timing configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npatcfg1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npatcfg1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@npatcfg1`]
module"]
#[doc(alias = "NPATCFG1")]
pub type Npatcfg1 = crate::Reg<npatcfg1::Npatcfg1Spec>;
#[doc = "NAND flash/PC card attribute space timing configuration register 1"]
pub mod npatcfg1;
#[doc = "NPATCFG2 (rw) register accessor: NAND flash/PC card attribute space timing configuration register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npatcfg2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npatcfg2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@npatcfg2`]
module"]
#[doc(alias = "NPATCFG2")]
pub type Npatcfg2 = crate::Reg<npatcfg2::Npatcfg2Spec>;
#[doc = "NAND flash/PC card attribute space timing configuration register 2"]
pub mod npatcfg2;
#[doc = "NPATCFG3 (rw) register accessor: NAND flash/PC card attribute space timing configuration register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npatcfg3::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npatcfg3::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@npatcfg3`]
module"]
#[doc(alias = "NPATCFG3")]
pub type Npatcfg3 = crate::Reg<npatcfg3::Npatcfg3Spec>;
#[doc = "NAND flash/PC card attribute space timing configuration register 3"]
pub mod npatcfg3;
#[doc = "PIOTCFG3 (rw) register accessor: PC card I/O space timing configuration register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`piotcfg3::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`piotcfg3::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@piotcfg3`]
module"]
#[doc(alias = "PIOTCFG3")]
pub type Piotcfg3 = crate::Reg<piotcfg3::Piotcfg3Spec>;
#[doc = "PC card I/O space timing configuration register"]
pub mod piotcfg3;
#[doc = "NECC1 (r) register accessor: NAND flash ECC register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`necc1::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@necc1`]
module"]
#[doc(alias = "NECC1")]
pub type Necc1 = crate::Reg<necc1::Necc1Spec>;
#[doc = "NAND flash ECC register 1"]
pub mod necc1;
#[doc = "NECC2 (r) register accessor: NAND flash ECC register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`necc2::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@necc2`]
module"]
#[doc(alias = "NECC2")]
pub type Necc2 = crate::Reg<necc2::Necc2Spec>;
#[doc = "NAND flash ECC register 2"]
pub mod necc2;
