#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    dma_bctl: DmaBctl,
    dma_tpen: DmaTpen,
    dma_rpen: DmaRpen,
    dma_rdtaddr: DmaRdtaddr,
    dma_tdtaddr: DmaTdtaddr,
    dma_stat: DmaStat,
    dma_ctl: DmaCtl,
    dma_inten: DmaInten,
    dma_mfbocnt: DmaMfbocnt,
    dma_rswdc: DmaRswdc,
    _reserved10: [u8; 0x20],
    dma_ctdaddr: DmaCtdaddr,
    dma_crdaddr: DmaCrdaddr,
    dma_ctbaddr: DmaCtbaddr,
    dma_crbaddr: DmaCrbaddr,
}
impl RegisterBlock {
    #[doc = "0x00 - Ethernet DMA bus control register"]
    #[inline(always)]
    pub const fn dma_bctl(&self) -> &DmaBctl {
        &self.dma_bctl
    }
    #[doc = "0x04 - Ethernet DMA transmit poll enable register"]
    #[inline(always)]
    pub const fn dma_tpen(&self) -> &DmaTpen {
        &self.dma_tpen
    }
    #[doc = "0x08 - Ethernet DMA receive poll enable register"]
    #[inline(always)]
    pub const fn dma_rpen(&self) -> &DmaRpen {
        &self.dma_rpen
    }
    #[doc = "0x0c - Ethernet DMA receive descriptor table address register"]
    #[inline(always)]
    pub const fn dma_rdtaddr(&self) -> &DmaRdtaddr {
        &self.dma_rdtaddr
    }
    #[doc = "0x10 - Ethernet DMA transmit descriptor table address register"]
    #[inline(always)]
    pub const fn dma_tdtaddr(&self) -> &DmaTdtaddr {
        &self.dma_tdtaddr
    }
    #[doc = "0x14 - Ethernet DMA status register"]
    #[inline(always)]
    pub const fn dma_stat(&self) -> &DmaStat {
        &self.dma_stat
    }
    #[doc = "0x18 - Ethernet DMA control register"]
    #[inline(always)]
    pub const fn dma_ctl(&self) -> &DmaCtl {
        &self.dma_ctl
    }
    #[doc = "0x1c - Ethernet DMA interrupt enable register"]
    #[inline(always)]
    pub const fn dma_inten(&self) -> &DmaInten {
        &self.dma_inten
    }
    #[doc = "0x20 - Ethernet DMA missed frame and buffer overflow counter register"]
    #[inline(always)]
    pub const fn dma_mfbocnt(&self) -> &DmaMfbocnt {
        &self.dma_mfbocnt
    }
    #[doc = "0x24 - Ethernet DMA receive state watchdog counter register"]
    #[inline(always)]
    pub const fn dma_rswdc(&self) -> &DmaRswdc {
        &self.dma_rswdc
    }
    #[doc = "0x48 - DMA current transmit descriptor address register"]
    #[inline(always)]
    pub const fn dma_ctdaddr(&self) -> &DmaCtdaddr {
        &self.dma_ctdaddr
    }
    #[doc = "0x4c - Ethernet DMA current receive descriptor address register"]
    #[inline(always)]
    pub const fn dma_crdaddr(&self) -> &DmaCrdaddr {
        &self.dma_crdaddr
    }
    #[doc = "0x50 - Ethernet DMA current transmit buffer address register"]
    #[inline(always)]
    pub const fn dma_ctbaddr(&self) -> &DmaCtbaddr {
        &self.dma_ctbaddr
    }
    #[doc = "0x54 - Ethernet DMA current receive buffer address register"]
    #[inline(always)]
    pub const fn dma_crbaddr(&self) -> &DmaCrbaddr {
        &self.dma_crbaddr
    }
}
#[doc = "DMA_BCTL (rw) register accessor: Ethernet DMA bus control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_bctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_bctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_bctl`]
module"]
#[doc(alias = "DMA_BCTL")]
pub type DmaBctl = crate::Reg<dma_bctl::DmaBctlSpec>;
#[doc = "Ethernet DMA bus control register"]
pub mod dma_bctl;
#[doc = "DMA_TPEN (rw) register accessor: Ethernet DMA transmit poll enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_tpen::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_tpen::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_tpen`]
module"]
#[doc(alias = "DMA_TPEN")]
pub type DmaTpen = crate::Reg<dma_tpen::DmaTpenSpec>;
#[doc = "Ethernet DMA transmit poll enable register"]
pub mod dma_tpen;
#[doc = "DMA_RPEN (rw) register accessor: Ethernet DMA receive poll enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_rpen::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_rpen::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_rpen`]
module"]
#[doc(alias = "DMA_RPEN")]
pub type DmaRpen = crate::Reg<dma_rpen::DmaRpenSpec>;
#[doc = "Ethernet DMA receive poll enable register"]
pub mod dma_rpen;
#[doc = "DMA_RDTADDR (rw) register accessor: Ethernet DMA receive descriptor table address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_rdtaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_rdtaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_rdtaddr`]
module"]
#[doc(alias = "DMA_RDTADDR")]
pub type DmaRdtaddr = crate::Reg<dma_rdtaddr::DmaRdtaddrSpec>;
#[doc = "Ethernet DMA receive descriptor table address register"]
pub mod dma_rdtaddr;
#[doc = "DMA_TDTADDR (rw) register accessor: Ethernet DMA transmit descriptor table address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_tdtaddr::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_tdtaddr::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_tdtaddr`]
module"]
#[doc(alias = "DMA_TDTADDR")]
pub type DmaTdtaddr = crate::Reg<dma_tdtaddr::DmaTdtaddrSpec>;
#[doc = "Ethernet DMA transmit descriptor table address register"]
pub mod dma_tdtaddr;
#[doc = "DMA_STAT (rw) register accessor: Ethernet DMA status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_stat::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_stat::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_stat`]
module"]
#[doc(alias = "DMA_STAT")]
pub type DmaStat = crate::Reg<dma_stat::DmaStatSpec>;
#[doc = "Ethernet DMA status register"]
pub mod dma_stat;
#[doc = "DMA_CTL (rw) register accessor: Ethernet DMA control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_ctl`]
module"]
#[doc(alias = "DMA_CTL")]
pub type DmaCtl = crate::Reg<dma_ctl::DmaCtlSpec>;
#[doc = "Ethernet DMA control register"]
pub mod dma_ctl;
#[doc = "DMA_INTEN (rw) register accessor: Ethernet DMA interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_inten`]
module"]
#[doc(alias = "DMA_INTEN")]
pub type DmaInten = crate::Reg<dma_inten::DmaIntenSpec>;
#[doc = "Ethernet DMA interrupt enable register"]
pub mod dma_inten;
#[doc = "DMA_MFBOCNT (r) register accessor: Ethernet DMA missed frame and buffer overflow counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_mfbocnt::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_mfbocnt`]
module"]
#[doc(alias = "DMA_MFBOCNT")]
pub type DmaMfbocnt = crate::Reg<dma_mfbocnt::DmaMfbocntSpec>;
#[doc = "Ethernet DMA missed frame and buffer overflow counter register"]
pub mod dma_mfbocnt;
#[doc = "DMA_RSWDC (rw) register accessor: Ethernet DMA receive state watchdog counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_rswdc::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_rswdc::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_rswdc`]
module"]
#[doc(alias = "DMA_RSWDC")]
pub type DmaRswdc = crate::Reg<dma_rswdc::DmaRswdcSpec>;
#[doc = "Ethernet DMA receive state watchdog counter register"]
pub mod dma_rswdc;
#[doc = "DMA_CTDADDR (r) register accessor: DMA current transmit descriptor address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_ctdaddr::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_ctdaddr`]
module"]
#[doc(alias = "DMA_CTDADDR")]
pub type DmaCtdaddr = crate::Reg<dma_ctdaddr::DmaCtdaddrSpec>;
#[doc = "DMA current transmit descriptor address register"]
pub mod dma_ctdaddr;
#[doc = "DMA_CRDADDR (r) register accessor: Ethernet DMA current receive descriptor address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_crdaddr::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_crdaddr`]
module"]
#[doc(alias = "DMA_CRDADDR")]
pub type DmaCrdaddr = crate::Reg<dma_crdaddr::DmaCrdaddrSpec>;
#[doc = "Ethernet DMA current receive descriptor address register"]
pub mod dma_crdaddr;
#[doc = "DMA_CTBADDR (r) register accessor: Ethernet DMA current transmit buffer address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_ctbaddr::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_ctbaddr`]
module"]
#[doc(alias = "DMA_CTBADDR")]
pub type DmaCtbaddr = crate::Reg<dma_ctbaddr::DmaCtbaddrSpec>;
#[doc = "Ethernet DMA current transmit buffer address register"]
pub mod dma_ctbaddr;
#[doc = "DMA_CRBADDR (r) register accessor: Ethernet DMA current receive buffer address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_crbaddr::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_crbaddr`]
module"]
#[doc(alias = "DMA_CRBADDR")]
pub type DmaCrbaddr = crate::Reg<dma_crbaddr::DmaCrbaddrSpec>;
#[doc = "Ethernet DMA current receive buffer address register"]
pub mod dma_crbaddr;
