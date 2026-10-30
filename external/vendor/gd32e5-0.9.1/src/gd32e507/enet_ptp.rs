#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    ptp_tsctl: PtpTsctl,
    ptp_ssinc: PtpSsinc,
    ptp_tsh: PtpTsh,
    ptp_tsl: PtpTsl,
    ptp_tsuh: PtpTsuh,
    ptp_tsul: PtpTsul,
    ptp_tsaddend: PtpTsaddend,
    ptp_eth: PtpEth,
    ptp_etl: PtpEtl,
    _reserved9: [u8; 0x04],
    ptp_tsf: PtpTsf,
    ptp_ppsctl: PtpPpsctl,
}
impl RegisterBlock {
    #[doc = "0x00 - Ethernet PTP time stamp control register (PTP_TSCTL)"]
    #[inline(always)]
    pub const fn ptp_tsctl(&self) -> &PtpTsctl {
        &self.ptp_tsctl
    }
    #[doc = "0x04 - Ethernet PTP subsecond increment register"]
    #[inline(always)]
    pub const fn ptp_ssinc(&self) -> &PtpSsinc {
        &self.ptp_ssinc
    }
    #[doc = "0x08 - Ethernet PTP time stamp high register"]
    #[inline(always)]
    pub const fn ptp_tsh(&self) -> &PtpTsh {
        &self.ptp_tsh
    }
    #[doc = "0x0c - Ethernet PTP time stamp low register (PTP_TSL)"]
    #[inline(always)]
    pub const fn ptp_tsl(&self) -> &PtpTsl {
        &self.ptp_tsl
    }
    #[doc = "0x10 - Ethernet PTP time stamp high update register"]
    #[inline(always)]
    pub const fn ptp_tsuh(&self) -> &PtpTsuh {
        &self.ptp_tsuh
    }
    #[doc = "0x14 - Ethernet PTP time stamp low update register (PTP_TSUL)"]
    #[inline(always)]
    pub const fn ptp_tsul(&self) -> &PtpTsul {
        &self.ptp_tsul
    }
    #[doc = "0x18 - Ethernet PTP time stamp addend register"]
    #[inline(always)]
    pub const fn ptp_tsaddend(&self) -> &PtpTsaddend {
        &self.ptp_tsaddend
    }
    #[doc = "0x1c - Ethernet PTP expected time high register"]
    #[inline(always)]
    pub const fn ptp_eth(&self) -> &PtpEth {
        &self.ptp_eth
    }
    #[doc = "0x20 - Ethernet PTP expected time low register"]
    #[inline(always)]
    pub const fn ptp_etl(&self) -> &PtpEtl {
        &self.ptp_etl
    }
    #[doc = "0x28 - Ethernet PTP time stamp flag register"]
    #[inline(always)]
    pub const fn ptp_tsf(&self) -> &PtpTsf {
        &self.ptp_tsf
    }
    #[doc = "0x2c - Ethernet PTP PPS control register"]
    #[inline(always)]
    pub const fn ptp_ppsctl(&self) -> &PtpPpsctl {
        &self.ptp_ppsctl
    }
}
#[doc = "PTP_TSCTL (rw) register accessor: Ethernet PTP time stamp control register (PTP_TSCTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_tsctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ptp_tsctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ptp_tsctl`]
module"]
#[doc(alias = "PTP_TSCTL")]
pub type PtpTsctl = crate::Reg<ptp_tsctl::PtpTsctlSpec>;
#[doc = "Ethernet PTP time stamp control register (PTP_TSCTL)"]
pub mod ptp_tsctl;
#[doc = "PTP_SSINC (rw) register accessor: Ethernet PTP subsecond increment register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_ssinc::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ptp_ssinc::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ptp_ssinc`]
module"]
#[doc(alias = "PTP_SSINC")]
pub type PtpSsinc = crate::Reg<ptp_ssinc::PtpSsincSpec>;
#[doc = "Ethernet PTP subsecond increment register"]
pub mod ptp_ssinc;
#[doc = "PTP_TSH (r) register accessor: Ethernet PTP time stamp high register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_tsh::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ptp_tsh`]
module"]
#[doc(alias = "PTP_TSH")]
pub type PtpTsh = crate::Reg<ptp_tsh::PtpTshSpec>;
#[doc = "Ethernet PTP time stamp high register"]
pub mod ptp_tsh;
#[doc = "PTP_TSL (r) register accessor: Ethernet PTP time stamp low register (PTP_TSL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_tsl::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ptp_tsl`]
module"]
#[doc(alias = "PTP_TSL")]
pub type PtpTsl = crate::Reg<ptp_tsl::PtpTslSpec>;
#[doc = "Ethernet PTP time stamp low register (PTP_TSL)"]
pub mod ptp_tsl;
#[doc = "PTP_TSUH (rw) register accessor: Ethernet PTP time stamp high update register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_tsuh::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ptp_tsuh::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ptp_tsuh`]
module"]
#[doc(alias = "PTP_TSUH")]
pub type PtpTsuh = crate::Reg<ptp_tsuh::PtpTsuhSpec>;
#[doc = "Ethernet PTP time stamp high update register"]
pub mod ptp_tsuh;
#[doc = "PTP_TSUL (rw) register accessor: Ethernet PTP time stamp low update register (PTP_TSUL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_tsul::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ptp_tsul::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ptp_tsul`]
module"]
#[doc(alias = "PTP_TSUL")]
pub type PtpTsul = crate::Reg<ptp_tsul::PtpTsulSpec>;
#[doc = "Ethernet PTP time stamp low update register (PTP_TSUL)"]
pub mod ptp_tsul;
#[doc = "PTP_TSADDEND (rw) register accessor: Ethernet PTP time stamp addend register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_tsaddend::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ptp_tsaddend::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ptp_tsaddend`]
module"]
#[doc(alias = "PTP_TSADDEND")]
pub type PtpTsaddend = crate::Reg<ptp_tsaddend::PtpTsaddendSpec>;
#[doc = "Ethernet PTP time stamp addend register"]
pub mod ptp_tsaddend;
#[doc = "PTP_ETH (rw) register accessor: Ethernet PTP expected time high register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_eth::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ptp_eth::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ptp_eth`]
module"]
#[doc(alias = "PTP_ETH")]
pub type PtpEth = crate::Reg<ptp_eth::PtpEthSpec>;
#[doc = "Ethernet PTP expected time high register"]
pub mod ptp_eth;
#[doc = "PTP_ETL (rw) register accessor: Ethernet PTP expected time low register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_etl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ptp_etl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ptp_etl`]
module"]
#[doc(alias = "PTP_ETL")]
pub type PtpEtl = crate::Reg<ptp_etl::PtpEtlSpec>;
#[doc = "Ethernet PTP expected time low register"]
pub mod ptp_etl;
#[doc = "PTP_TSF (r) register accessor: Ethernet PTP time stamp flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_tsf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ptp_tsf`]
module"]
#[doc(alias = "PTP_TSF")]
pub type PtpTsf = crate::Reg<ptp_tsf::PtpTsfSpec>;
#[doc = "Ethernet PTP time stamp flag register"]
pub mod ptp_tsf;
#[doc = "PTP_PPSCTL (rw) register accessor: Ethernet PTP PPS control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_ppsctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ptp_ppsctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ptp_ppsctl`]
module"]
#[doc(alias = "PTP_PPSCTL")]
pub type PtpPpsctl = crate::Reg<ptp_ppsctl::PtpPpsctlSpec>;
#[doc = "Ethernet PTP PPS control register"]
pub mod ptp_ppsctl;
