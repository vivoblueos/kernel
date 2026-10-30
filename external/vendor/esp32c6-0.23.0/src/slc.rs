#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    slcconf0: SLCCONF0,
    slc0int_raw: SLC0INT_RAW,
    slc0int_st: SLC0INT_ST,
    slc0int_ena: SLC0INT_ENA,
    slc0int_clr: SLC0INT_CLR,
    slc1int_raw: SLC1INT_RAW,
    _reserved6: [u8; 0x08],
    slc1int_clr: SLC1INT_CLR,
    _reserved7: [u8; 0x18],
    slc0rx_link: SLC0RX_LINK,
    slc0rx_link_addr: SLC0RX_LINK_ADDR,
    slc0tx_link: SLC0TX_LINK,
    slc0tx_link_addr: SLC0TX_LINK_ADDR,
    slc1rx_link: SLC1RX_LINK,
    slc1rx_link_addr: SLC1RX_LINK_ADDR,
    slc1tx_link: SLC1TX_LINK,
    slc1tx_link_addr: SLC1TX_LINK_ADDR,
    slcintvec_tohost: SLCINTVEC_TOHOST,
    _reserved16: [u8; 0x04],
    slc0token1: SLC0TOKEN1,
    _reserved17: [u8; 0x04],
    slc1token1: SLC1TOKEN1,
    slcconf1: SLCCONF1,
    _reserved19: [u8; 0x34],
    slc_rx_dscr_conf: SLC_RX_DSCR_CONF,
    _reserved20: [u8; 0x48],
    slc0_len_conf: SLC0_LEN_CONF,
    slc0_length: SLC0_LENGTH,
    _reserved22: [u8; 0x50],
    slc1int_st1: SLC1INT_ST1,
    slc1int_ena1: SLC1INT_ENA1,
    slc0_tx_sharemem_start: SLC0_TX_SHAREMEM_START,
    slc0_tx_sharemem_end: SLC0_TX_SHAREMEM_END,
    slc0_rx_sharemem_start: SLC0_RX_SHAREMEM_START,
    slc0_rx_sharemem_end: SLC0_RX_SHAREMEM_END,
    slc1_tx_sharemem_start: SLC1_TX_SHAREMEM_START,
    slc1_tx_sharemem_end: SLC1_TX_SHAREMEM_END,
    slc1_rx_sharemem_start: SLC1_RX_SHAREMEM_START,
    slc1_rx_sharemem_end: SLC1_RX_SHAREMEM_END,
    _reserved32: [u8; 0x08],
    slc_burst_len: SLC_BURST_LEN,
}
impl RegisterBlock {
    #[doc = "0x00 - DMA configuration"]
    #[inline(always)]
    pub const fn slcconf0(&self) -> &SLCCONF0 {
        &self.slcconf0
    }
    #[doc = "0x04 - SLC0 to slave raw interrupt status"]
    #[inline(always)]
    pub const fn slc0int_raw(&self) -> &SLC0INT_RAW {
        &self.slc0int_raw
    }
    #[doc = "0x08 - SLC0 to slave masked interrupt status"]
    #[inline(always)]
    pub const fn slc0int_st(&self) -> &SLC0INT_ST {
        &self.slc0int_st
    }
    #[doc = "0x0c - SLC0 to slave interrupt enable"]
    #[inline(always)]
    pub const fn slc0int_ena(&self) -> &SLC0INT_ENA {
        &self.slc0int_ena
    }
    #[doc = "0x10 - SLC0 to slave interrupt clear"]
    #[inline(always)]
    pub const fn slc0int_clr(&self) -> &SLC0INT_CLR {
        &self.slc0int_clr
    }
    #[doc = "0x14 - SLC1 to slave raw interrupt status"]
    #[inline(always)]
    pub const fn slc1int_raw(&self) -> &SLC1INT_RAW {
        &self.slc1int_raw
    }
    #[doc = "0x20 - SLC1 to slave interrupt clear"]
    #[inline(always)]
    pub const fn slc1int_clr(&self) -> &SLC1INT_CLR {
        &self.slc1int_clr
    }
    #[doc = "0x3c - SLC0 RX linked list configuration"]
    #[inline(always)]
    pub const fn slc0rx_link(&self) -> &SLC0RX_LINK {
        &self.slc0rx_link
    }
    #[doc = "0x40 - SLC0 RX linked list address"]
    #[inline(always)]
    pub const fn slc0rx_link_addr(&self) -> &SLC0RX_LINK_ADDR {
        &self.slc0rx_link_addr
    }
    #[doc = "0x44 - SLC0 TX linked list configuration"]
    #[inline(always)]
    pub const fn slc0tx_link(&self) -> &SLC0TX_LINK {
        &self.slc0tx_link
    }
    #[doc = "0x48 - SLC0 TX linked list address"]
    #[inline(always)]
    pub const fn slc0tx_link_addr(&self) -> &SLC0TX_LINK_ADDR {
        &self.slc0tx_link_addr
    }
    #[doc = "0x4c - SLC1 RX linked list configuration"]
    #[inline(always)]
    pub const fn slc1rx_link(&self) -> &SLC1RX_LINK {
        &self.slc1rx_link
    }
    #[doc = "0x50 - SLC1 RX linked list address"]
    #[inline(always)]
    pub const fn slc1rx_link_addr(&self) -> &SLC1RX_LINK_ADDR {
        &self.slc1rx_link_addr
    }
    #[doc = "0x54 - SLC1 TX linked list configuration"]
    #[inline(always)]
    pub const fn slc1tx_link(&self) -> &SLC1TX_LINK {
        &self.slc1tx_link
    }
    #[doc = "0x58 - SLC1 TX linked list address"]
    #[inline(always)]
    pub const fn slc1tx_link_addr(&self) -> &SLC1TX_LINK_ADDR {
        &self.slc1tx_link_addr
    }
    #[doc = "0x5c - Slave to host interrupt vector set"]
    #[inline(always)]
    pub const fn slcintvec_tohost(&self) -> &SLCINTVEC_TOHOST {
        &self.slcintvec_tohost
    }
    #[doc = "0x64 - SLC0 receiving buffer configuration"]
    #[inline(always)]
    pub const fn slc0token1(&self) -> &SLC0TOKEN1 {
        &self.slc0token1
    }
    #[doc = "0x6c - SLC1 receiving buffer configuration"]
    #[inline(always)]
    pub const fn slc1token1(&self) -> &SLC1TOKEN1 {
        &self.slc1token1
    }
    #[doc = "0x70 - DMA configuration"]
    #[inline(always)]
    pub const fn slcconf1(&self) -> &SLCCONF1 {
        &self.slcconf1
    }
    #[doc = "0xa8 - DMA slave to host configuration register"]
    #[inline(always)]
    pub const fn slc_rx_dscr_conf(&self) -> &SLC_RX_DSCR_CONF {
        &self.slc_rx_dscr_conf
    }
    #[doc = "0xf4 - Length control of transmitting packets"]
    #[inline(always)]
    pub const fn slc0_len_conf(&self) -> &SLC0_LEN_CONF {
        &self.slc0_len_conf
    }
    #[doc = "0xf8 - Length of transmitting packets"]
    #[inline(always)]
    pub const fn slc0_length(&self) -> &SLC0_LENGTH {
        &self.slc0_length
    }
    #[doc = "0x14c - SLC1 to slave masked interrupt status"]
    #[inline(always)]
    pub const fn slc1int_st1(&self) -> &SLC1INT_ST1 {
        &self.slc1int_st1
    }
    #[doc = "0x150 - SLC1 to slave interrupt enable"]
    #[inline(always)]
    pub const fn slc1int_ena1(&self) -> &SLC1INT_ENA1 {
        &self.slc1int_ena1
    }
    #[doc = "0x154 - SLC0 AHB TX start address range"]
    #[inline(always)]
    pub const fn slc0_tx_sharemem_start(&self) -> &SLC0_TX_SHAREMEM_START {
        &self.slc0_tx_sharemem_start
    }
    #[doc = "0x158 - SLC0 AHB TX end address range"]
    #[inline(always)]
    pub const fn slc0_tx_sharemem_end(&self) -> &SLC0_TX_SHAREMEM_END {
        &self.slc0_tx_sharemem_end
    }
    #[doc = "0x15c - SLC0 AHB RX start address range"]
    #[inline(always)]
    pub const fn slc0_rx_sharemem_start(&self) -> &SLC0_RX_SHAREMEM_START {
        &self.slc0_rx_sharemem_start
    }
    #[doc = "0x160 - SLC0 AHB RX end address range"]
    #[inline(always)]
    pub const fn slc0_rx_sharemem_end(&self) -> &SLC0_RX_SHAREMEM_END {
        &self.slc0_rx_sharemem_end
    }
    #[doc = "0x164 - SLC1 AHB TX start address range"]
    #[inline(always)]
    pub const fn slc1_tx_sharemem_start(&self) -> &SLC1_TX_SHAREMEM_START {
        &self.slc1_tx_sharemem_start
    }
    #[doc = "0x168 - SLC1 AHB TX end address range"]
    #[inline(always)]
    pub const fn slc1_tx_sharemem_end(&self) -> &SLC1_TX_SHAREMEM_END {
        &self.slc1_tx_sharemem_end
    }
    #[doc = "0x16c - SLC1 AHB RX start address range"]
    #[inline(always)]
    pub const fn slc1_rx_sharemem_start(&self) -> &SLC1_RX_SHAREMEM_START {
        &self.slc1_rx_sharemem_start
    }
    #[doc = "0x170 - SLC1 AHB RX end address range"]
    #[inline(always)]
    pub const fn slc1_rx_sharemem_end(&self) -> &SLC1_RX_SHAREMEM_END {
        &self.slc1_rx_sharemem_end
    }
    #[doc = "0x17c - DMA AHB burst type configuration"]
    #[inline(always)]
    pub const fn slc_burst_len(&self) -> &SLC_BURST_LEN {
        &self.slc_burst_len
    }
}
#[doc = "SLCCONF0 (rw) register accessor: DMA configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slcconf0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slcconf0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slcconf0`] module"]
pub type SLCCONF0 = crate::Reg<slcconf0::SLCCONF0_SPEC>;
#[doc = "DMA configuration"]
pub mod slcconf0;
#[doc = "SLC0RX_LINK (rw) register accessor: SLC0 RX linked list configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0rx_link::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0rx_link::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0rx_link`] module"]
pub type SLC0RX_LINK = crate::Reg<slc0rx_link::SLC0RX_LINK_SPEC>;
#[doc = "SLC0 RX linked list configuration"]
pub mod slc0rx_link;
#[doc = "SLC0RX_LINK_ADDR (rw) register accessor: SLC0 RX linked list address\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0rx_link_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0rx_link_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0rx_link_addr`] module"]
pub type SLC0RX_LINK_ADDR = crate::Reg<slc0rx_link_addr::SLC0RX_LINK_ADDR_SPEC>;
#[doc = "SLC0 RX linked list address"]
pub mod slc0rx_link_addr;
#[doc = "SLC0TX_LINK (rw) register accessor: SLC0 TX linked list configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0tx_link::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0tx_link::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0tx_link`] module"]
pub type SLC0TX_LINK = crate::Reg<slc0tx_link::SLC0TX_LINK_SPEC>;
#[doc = "SLC0 TX linked list configuration"]
pub mod slc0tx_link;
#[doc = "SLC0TX_LINK_ADDR (rw) register accessor: SLC0 TX linked list address\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0tx_link_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0tx_link_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0tx_link_addr`] module"]
pub type SLC0TX_LINK_ADDR = crate::Reg<slc0tx_link_addr::SLC0TX_LINK_ADDR_SPEC>;
#[doc = "SLC0 TX linked list address"]
pub mod slc0tx_link_addr;
#[doc = "SLC1RX_LINK (rw) register accessor: SLC1 RX linked list configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1rx_link::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1rx_link::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1rx_link`] module"]
pub type SLC1RX_LINK = crate::Reg<slc1rx_link::SLC1RX_LINK_SPEC>;
#[doc = "SLC1 RX linked list configuration"]
pub mod slc1rx_link;
#[doc = "SLC1RX_LINK_ADDR (rw) register accessor: SLC1 RX linked list address\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1rx_link_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1rx_link_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1rx_link_addr`] module"]
pub type SLC1RX_LINK_ADDR = crate::Reg<slc1rx_link_addr::SLC1RX_LINK_ADDR_SPEC>;
#[doc = "SLC1 RX linked list address"]
pub mod slc1rx_link_addr;
#[doc = "SLC1TX_LINK (rw) register accessor: SLC1 TX linked list configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1tx_link::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1tx_link::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1tx_link`] module"]
pub type SLC1TX_LINK = crate::Reg<slc1tx_link::SLC1TX_LINK_SPEC>;
#[doc = "SLC1 TX linked list configuration"]
pub mod slc1tx_link;
#[doc = "SLC1TX_LINK_ADDR (rw) register accessor: SLC1 TX linked list address\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1tx_link_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1tx_link_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1tx_link_addr`] module"]
pub type SLC1TX_LINK_ADDR = crate::Reg<slc1tx_link_addr::SLC1TX_LINK_ADDR_SPEC>;
#[doc = "SLC1 TX linked list address"]
pub mod slc1tx_link_addr;
#[doc = "SLC0TOKEN1 (rw) register accessor: SLC0 receiving buffer configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0token1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0token1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0token1`] module"]
pub type SLC0TOKEN1 = crate::Reg<slc0token1::SLC0TOKEN1_SPEC>;
#[doc = "SLC0 receiving buffer configuration"]
pub mod slc0token1;
#[doc = "SLC1TOKEN1 (rw) register accessor: SLC1 receiving buffer configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1token1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1token1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1token1`] module"]
pub type SLC1TOKEN1 = crate::Reg<slc1token1::SLC1TOKEN1_SPEC>;
#[doc = "SLC1 receiving buffer configuration"]
pub mod slc1token1;
#[doc = "SLCCONF1 (rw) register accessor: DMA configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slcconf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slcconf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slcconf1`] module"]
pub type SLCCONF1 = crate::Reg<slcconf1::SLCCONF1_SPEC>;
#[doc = "DMA configuration"]
pub mod slcconf1;
#[doc = "SLC_RX_DSCR_CONF (rw) register accessor: DMA slave to host configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`slc_rx_dscr_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc_rx_dscr_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc_rx_dscr_conf`] module"]
pub type SLC_RX_DSCR_CONF = crate::Reg<slc_rx_dscr_conf::SLC_RX_DSCR_CONF_SPEC>;
#[doc = "DMA slave to host configuration register"]
pub mod slc_rx_dscr_conf;
#[doc = "SLC0_LEN_CONF (w) register accessor: Length control of transmitting packets\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0_len_conf::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0_len_conf`] module"]
pub type SLC0_LEN_CONF = crate::Reg<slc0_len_conf::SLC0_LEN_CONF_SPEC>;
#[doc = "Length control of transmitting packets"]
pub mod slc0_len_conf;
#[doc = "SLC0_TX_SHAREMEM_START (rw) register accessor: SLC0 AHB TX start address range\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0_tx_sharemem_start::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0_tx_sharemem_start::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0_tx_sharemem_start`] module"]
pub type SLC0_TX_SHAREMEM_START = crate::Reg<slc0_tx_sharemem_start::SLC0_TX_SHAREMEM_START_SPEC>;
#[doc = "SLC0 AHB TX start address range"]
pub mod slc0_tx_sharemem_start;
#[doc = "SLC0_TX_SHAREMEM_END (rw) register accessor: SLC0 AHB TX end address range\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0_tx_sharemem_end::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0_tx_sharemem_end::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0_tx_sharemem_end`] module"]
pub type SLC0_TX_SHAREMEM_END = crate::Reg<slc0_tx_sharemem_end::SLC0_TX_SHAREMEM_END_SPEC>;
#[doc = "SLC0 AHB TX end address range"]
pub mod slc0_tx_sharemem_end;
#[doc = "SLC0_RX_SHAREMEM_START (rw) register accessor: SLC0 AHB RX start address range\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0_rx_sharemem_start::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0_rx_sharemem_start::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0_rx_sharemem_start`] module"]
pub type SLC0_RX_SHAREMEM_START = crate::Reg<slc0_rx_sharemem_start::SLC0_RX_SHAREMEM_START_SPEC>;
#[doc = "SLC0 AHB RX start address range"]
pub mod slc0_rx_sharemem_start;
#[doc = "SLC0_RX_SHAREMEM_END (rw) register accessor: SLC0 AHB RX end address range\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0_rx_sharemem_end::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0_rx_sharemem_end::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0_rx_sharemem_end`] module"]
pub type SLC0_RX_SHAREMEM_END = crate::Reg<slc0_rx_sharemem_end::SLC0_RX_SHAREMEM_END_SPEC>;
#[doc = "SLC0 AHB RX end address range"]
pub mod slc0_rx_sharemem_end;
#[doc = "SLC1_TX_SHAREMEM_START (rw) register accessor: SLC1 AHB TX start address range\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1_tx_sharemem_start::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1_tx_sharemem_start::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1_tx_sharemem_start`] module"]
pub type SLC1_TX_SHAREMEM_START = crate::Reg<slc1_tx_sharemem_start::SLC1_TX_SHAREMEM_START_SPEC>;
#[doc = "SLC1 AHB TX start address range"]
pub mod slc1_tx_sharemem_start;
#[doc = "SLC1_TX_SHAREMEM_END (rw) register accessor: SLC1 AHB TX end address range\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1_tx_sharemem_end::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1_tx_sharemem_end::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1_tx_sharemem_end`] module"]
pub type SLC1_TX_SHAREMEM_END = crate::Reg<slc1_tx_sharemem_end::SLC1_TX_SHAREMEM_END_SPEC>;
#[doc = "SLC1 AHB TX end address range"]
pub mod slc1_tx_sharemem_end;
#[doc = "SLC1_RX_SHAREMEM_START (rw) register accessor: SLC1 AHB RX start address range\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1_rx_sharemem_start::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1_rx_sharemem_start::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1_rx_sharemem_start`] module"]
pub type SLC1_RX_SHAREMEM_START = crate::Reg<slc1_rx_sharemem_start::SLC1_RX_SHAREMEM_START_SPEC>;
#[doc = "SLC1 AHB RX start address range"]
pub mod slc1_rx_sharemem_start;
#[doc = "SLC1_RX_SHAREMEM_END (rw) register accessor: SLC1 AHB RX end address range\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1_rx_sharemem_end::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1_rx_sharemem_end::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1_rx_sharemem_end`] module"]
pub type SLC1_RX_SHAREMEM_END = crate::Reg<slc1_rx_sharemem_end::SLC1_RX_SHAREMEM_END_SPEC>;
#[doc = "SLC1 AHB RX end address range"]
pub mod slc1_rx_sharemem_end;
#[doc = "SLC_BURST_LEN (rw) register accessor: DMA AHB burst type configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`slc_burst_len::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc_burst_len::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc_burst_len`] module"]
pub type SLC_BURST_LEN = crate::Reg<slc_burst_len::SLC_BURST_LEN_SPEC>;
#[doc = "DMA AHB burst type configuration"]
pub mod slc_burst_len;
#[doc = "SLC0INT_RAW (rw) register accessor: SLC0 to slave raw interrupt status\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0int_raw::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0int_raw::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0int_raw`] module"]
pub type SLC0INT_RAW = crate::Reg<slc0int_raw::SLC0INT_RAW_SPEC>;
#[doc = "SLC0 to slave raw interrupt status"]
pub mod slc0int_raw;
#[doc = "SLC0INT_ST (r) register accessor: SLC0 to slave masked interrupt status\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0int_st`] module"]
pub type SLC0INT_ST = crate::Reg<slc0int_st::SLC0INT_ST_SPEC>;
#[doc = "SLC0 to slave masked interrupt status"]
pub mod slc0int_st;
#[doc = "SLC0INT_ENA (rw) register accessor: SLC0 to slave interrupt enable\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0int_ena`] module"]
pub type SLC0INT_ENA = crate::Reg<slc0int_ena::SLC0INT_ENA_SPEC>;
#[doc = "SLC0 to slave interrupt enable"]
pub mod slc0int_ena;
#[doc = "SLC0INT_CLR (w) register accessor: SLC0 to slave interrupt clear\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0int_clr`] module"]
pub type SLC0INT_CLR = crate::Reg<slc0int_clr::SLC0INT_CLR_SPEC>;
#[doc = "SLC0 to slave interrupt clear"]
pub mod slc0int_clr;
#[doc = "SLC1INT_RAW (rw) register accessor: SLC1 to slave raw interrupt status\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1int_raw::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1int_raw::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1int_raw`] module"]
pub type SLC1INT_RAW = crate::Reg<slc1int_raw::SLC1INT_RAW_SPEC>;
#[doc = "SLC1 to slave raw interrupt status"]
pub mod slc1int_raw;
#[doc = "SLC1INT_CLR (w) register accessor: SLC1 to slave interrupt clear\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1int_clr`] module"]
pub type SLC1INT_CLR = crate::Reg<slc1int_clr::SLC1INT_CLR_SPEC>;
#[doc = "SLC1 to slave interrupt clear"]
pub mod slc1int_clr;
#[doc = "SLCINTVEC_TOHOST (w) register accessor: Slave to host interrupt vector set\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slcintvec_tohost::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slcintvec_tohost`] module"]
pub type SLCINTVEC_TOHOST = crate::Reg<slcintvec_tohost::SLCINTVEC_TOHOST_SPEC>;
#[doc = "Slave to host interrupt vector set"]
pub mod slcintvec_tohost;
#[doc = "SLC1INT_ST1 (r) register accessor: SLC1 to slave masked interrupt status\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1int_st1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1int_st1`] module"]
pub type SLC1INT_ST1 = crate::Reg<slc1int_st1::SLC1INT_ST1_SPEC>;
#[doc = "SLC1 to slave masked interrupt status"]
pub mod slc1int_st1;
#[doc = "SLC1INT_ENA1 (rw) register accessor: SLC1 to slave interrupt enable\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1int_ena1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1int_ena1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1int_ena1`] module"]
pub type SLC1INT_ENA1 = crate::Reg<slc1int_ena1::SLC1INT_ENA1_SPEC>;
#[doc = "SLC1 to slave interrupt enable"]
pub mod slc1int_ena1;
#[doc = "SLC0_LENGTH (r) register accessor: Length of transmitting packets\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0_length::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0_length`] module"]
pub type SLC0_LENGTH = crate::Reg<slc0_length::SLC0_LENGTH_SPEC>;
#[doc = "Length of transmitting packets"]
pub mod slc0_length;
