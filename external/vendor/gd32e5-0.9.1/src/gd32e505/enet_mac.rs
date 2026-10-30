#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    mac_cfg: MacCfg,
    mac_frmf: MacFrmf,
    mac_hlh: MacHlh,
    mac_hll: MacHll,
    mac_phy_ctl: MacPhyCtl,
    mac_phy_data: MacPhyData,
    mac_fctl: MacFctl,
    mac_vlt: MacVlt,
    _reserved8: [u8; 0x08],
    mac_rwff: MacRwff,
    mac_wum: MacWum,
    _reserved10: [u8; 0x04],
    mac_dbg: MacDbg,
    mac_intf: MacIntf,
    mac_intmsk: MacIntmsk,
    mac_addr0h: MacAddr0h,
    mac_addr0l: MacAddr0l,
    mac_addr1h: MacAddr1h,
    mac_addr1l: MacAddr1l,
    mac_addr2h: MacAddr2h,
    mac_addr2l: MacAddr2l,
    mac_addr3h: MacAddr3h,
    mac_addr3l: MacAddr3l,
}
impl RegisterBlock {
    #[doc = "0x00 - Ethernet MAC configuration register (MAC_CFG)"]
    #[inline(always)]
    pub const fn mac_cfg(&self) -> &MacCfg {
        &self.mac_cfg
    }
    #[doc = "0x04 - Ethernet MAC frame filter register (MAC_FRMF)"]
    #[inline(always)]
    pub const fn mac_frmf(&self) -> &MacFrmf {
        &self.mac_frmf
    }
    #[doc = "0x08 - Ethernet MAC hash list high register"]
    #[inline(always)]
    pub const fn mac_hlh(&self) -> &MacHlh {
        &self.mac_hlh
    }
    #[doc = "0x0c - Ethernet MAC hash list low register"]
    #[inline(always)]
    pub const fn mac_hll(&self) -> &MacHll {
        &self.mac_hll
    }
    #[doc = "0x10 - Ethernet MAC PHY control register (MAC_PHY_CTL)"]
    #[inline(always)]
    pub const fn mac_phy_ctl(&self) -> &MacPhyCtl {
        &self.mac_phy_ctl
    }
    #[doc = "0x14 - Ethernet MAC MII data register (MAC_PHY_DATA)"]
    #[inline(always)]
    pub const fn mac_phy_data(&self) -> &MacPhyData {
        &self.mac_phy_data
    }
    #[doc = "0x18 - Ethernet MAC flow control register (MAC_FCTL)"]
    #[inline(always)]
    pub const fn mac_fctl(&self) -> &MacFctl {
        &self.mac_fctl
    }
    #[doc = "0x1c - Ethernet MAC VLAN tag register (MAC_VLT)"]
    #[inline(always)]
    pub const fn mac_vlt(&self) -> &MacVlt {
        &self.mac_vlt
    }
    #[doc = "0x28 - Ethernet MAC remote wakeup frame filter register (MAC_RWFF)"]
    #[inline(always)]
    pub const fn mac_rwff(&self) -> &MacRwff {
        &self.mac_rwff
    }
    #[doc = "0x2c - Ethernet MAC wakeup management register (MAC_WUM)"]
    #[inline(always)]
    pub const fn mac_wum(&self) -> &MacWum {
        &self.mac_wum
    }
    #[doc = "0x34 - Ethernet MAC debug register (MAC_DBG)"]
    #[inline(always)]
    pub const fn mac_dbg(&self) -> &MacDbg {
        &self.mac_dbg
    }
    #[doc = "0x38 - Ethernet MAC interrupt flag register (MAC_INTF)"]
    #[inline(always)]
    pub const fn mac_intf(&self) -> &MacIntf {
        &self.mac_intf
    }
    #[doc = "0x3c - Ethernet MAC interrupt mask register (MAC_INTMSK)"]
    #[inline(always)]
    pub const fn mac_intmsk(&self) -> &MacIntmsk {
        &self.mac_intmsk
    }
    #[doc = "0x40 - Ethernet MAC address 0 high register (MAC_ADDR0H)"]
    #[inline(always)]
    pub const fn mac_addr0h(&self) -> &MacAddr0h {
        &self.mac_addr0h
    }
    #[doc = "0x44 - Ethernet MAC address 0 low register"]
    #[inline(always)]
    pub const fn mac_addr0l(&self) -> &MacAddr0l {
        &self.mac_addr0l
    }
    #[doc = "0x48 - Ethernet MAC address 1 high register (MAC_ADDR1H)"]
    #[inline(always)]
    pub const fn mac_addr1h(&self) -> &MacAddr1h {
        &self.mac_addr1h
    }
    #[doc = "0x4c - Ethernet MAC address1 low register"]
    #[inline(always)]
    pub const fn mac_addr1l(&self) -> &MacAddr1l {
        &self.mac_addr1l
    }
    #[doc = "0x50 - Ethernet MAC address 2 high register (MAC_ADDR2H)"]
    #[inline(always)]
    pub const fn mac_addr2h(&self) -> &MacAddr2h {
        &self.mac_addr2h
    }
    #[doc = "0x54 - Ethernet MAC address 2 low register"]
    #[inline(always)]
    pub const fn mac_addr2l(&self) -> &MacAddr2l {
        &self.mac_addr2l
    }
    #[doc = "0x58 - Ethernet MAC address 3 high register (MAC_ADDR3H)"]
    #[inline(always)]
    pub const fn mac_addr3h(&self) -> &MacAddr3h {
        &self.mac_addr3h
    }
    #[doc = "0x5c - Ethernet MAC address 3 low register"]
    #[inline(always)]
    pub const fn mac_addr3l(&self) -> &MacAddr3l {
        &self.mac_addr3l
    }
}
#[doc = "MAC_CFG (rw) register accessor: Ethernet MAC configuration register (MAC_CFG)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_cfg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_cfg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_cfg`]
module"]
#[doc(alias = "MAC_CFG")]
pub type MacCfg = crate::Reg<mac_cfg::MacCfgSpec>;
#[doc = "Ethernet MAC configuration register (MAC_CFG)"]
pub mod mac_cfg;
#[doc = "MAC_FRMF (rw) register accessor: Ethernet MAC frame filter register (MAC_FRMF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_frmf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_frmf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_frmf`]
module"]
#[doc(alias = "MAC_FRMF")]
pub type MacFrmf = crate::Reg<mac_frmf::MacFrmfSpec>;
#[doc = "Ethernet MAC frame filter register (MAC_FRMF)"]
pub mod mac_frmf;
#[doc = "MAC_HLH (rw) register accessor: Ethernet MAC hash list high register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_hlh::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_hlh::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_hlh`]
module"]
#[doc(alias = "MAC_HLH")]
pub type MacHlh = crate::Reg<mac_hlh::MacHlhSpec>;
#[doc = "Ethernet MAC hash list high register"]
pub mod mac_hlh;
#[doc = "MAC_HLL (rw) register accessor: Ethernet MAC hash list low register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_hll::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_hll::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_hll`]
module"]
#[doc(alias = "MAC_HLL")]
pub type MacHll = crate::Reg<mac_hll::MacHllSpec>;
#[doc = "Ethernet MAC hash list low register"]
pub mod mac_hll;
#[doc = "MAC_PHY_CTL (rw) register accessor: Ethernet MAC PHY control register (MAC_PHY_CTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_phy_ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_phy_ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_phy_ctl`]
module"]
#[doc(alias = "MAC_PHY_CTL")]
pub type MacPhyCtl = crate::Reg<mac_phy_ctl::MacPhyCtlSpec>;
#[doc = "Ethernet MAC PHY control register (MAC_PHY_CTL)"]
pub mod mac_phy_ctl;
#[doc = "MAC_PHY_DATA (rw) register accessor: Ethernet MAC MII data register (MAC_PHY_DATA)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_phy_data::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_phy_data::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_phy_data`]
module"]
#[doc(alias = "MAC_PHY_DATA")]
pub type MacPhyData = crate::Reg<mac_phy_data::MacPhyDataSpec>;
#[doc = "Ethernet MAC MII data register (MAC_PHY_DATA)"]
pub mod mac_phy_data;
#[doc = "MAC_FCTL (rw) register accessor: Ethernet MAC flow control register (MAC_FCTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_fctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_fctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_fctl`]
module"]
#[doc(alias = "MAC_FCTL")]
pub type MacFctl = crate::Reg<mac_fctl::MacFctlSpec>;
#[doc = "Ethernet MAC flow control register (MAC_FCTL)"]
pub mod mac_fctl;
#[doc = "MAC_VLT (rw) register accessor: Ethernet MAC VLAN tag register (MAC_VLT)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_vlt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_vlt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_vlt`]
module"]
#[doc(alias = "MAC_VLT")]
pub type MacVlt = crate::Reg<mac_vlt::MacVltSpec>;
#[doc = "Ethernet MAC VLAN tag register (MAC_VLT)"]
pub mod mac_vlt;
#[doc = "MAC_RWFF (rw) register accessor: Ethernet MAC remote wakeup frame filter register (MAC_RWFF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_rwff::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_rwff::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_rwff`]
module"]
#[doc(alias = "MAC_RWFF")]
pub type MacRwff = crate::Reg<mac_rwff::MacRwffSpec>;
#[doc = "Ethernet MAC remote wakeup frame filter register (MAC_RWFF)"]
pub mod mac_rwff;
#[doc = "MAC_WUM (rw) register accessor: Ethernet MAC wakeup management register (MAC_WUM)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_wum::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_wum::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_wum`]
module"]
#[doc(alias = "MAC_WUM")]
pub type MacWum = crate::Reg<mac_wum::MacWumSpec>;
#[doc = "Ethernet MAC wakeup management register (MAC_WUM)"]
pub mod mac_wum;
#[doc = "MAC_DBG (r) register accessor: Ethernet MAC debug register (MAC_DBG)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_dbg::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_dbg`]
module"]
#[doc(alias = "MAC_DBG")]
pub type MacDbg = crate::Reg<mac_dbg::MacDbgSpec>;
#[doc = "Ethernet MAC debug register (MAC_DBG)"]
pub mod mac_dbg;
#[doc = "MAC_INTF (r) register accessor: Ethernet MAC interrupt flag register (MAC_INTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_intf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_intf`]
module"]
#[doc(alias = "MAC_INTF")]
pub type MacIntf = crate::Reg<mac_intf::MacIntfSpec>;
#[doc = "Ethernet MAC interrupt flag register (MAC_INTF)"]
pub mod mac_intf;
#[doc = "MAC_INTMSK (rw) register accessor: Ethernet MAC interrupt mask register (MAC_INTMSK)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_intmsk::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_intmsk::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_intmsk`]
module"]
#[doc(alias = "MAC_INTMSK")]
pub type MacIntmsk = crate::Reg<mac_intmsk::MacIntmskSpec>;
#[doc = "Ethernet MAC interrupt mask register (MAC_INTMSK)"]
pub mod mac_intmsk;
#[doc = "MAC_ADDR0H (rw) register accessor: Ethernet MAC address 0 high register (MAC_ADDR0H)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr0h::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr0h::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_addr0h`]
module"]
#[doc(alias = "MAC_ADDR0H")]
pub type MacAddr0h = crate::Reg<mac_addr0h::MacAddr0hSpec>;
#[doc = "Ethernet MAC address 0 high register (MAC_ADDR0H)"]
pub mod mac_addr0h;
#[doc = "MAC_ADDR0L (rw) register accessor: Ethernet MAC address 0 low register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr0l::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr0l::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_addr0l`]
module"]
#[doc(alias = "MAC_ADDR0L")]
pub type MacAddr0l = crate::Reg<mac_addr0l::MacAddr0lSpec>;
#[doc = "Ethernet MAC address 0 low register"]
pub mod mac_addr0l;
#[doc = "MAC_ADDR1H (rw) register accessor: Ethernet MAC address 1 high register (MAC_ADDR1H)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr1h::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr1h::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_addr1h`]
module"]
#[doc(alias = "MAC_ADDR1H")]
pub type MacAddr1h = crate::Reg<mac_addr1h::MacAddr1hSpec>;
#[doc = "Ethernet MAC address 1 high register (MAC_ADDR1H)"]
pub mod mac_addr1h;
#[doc = "MAC_ADDR1L (rw) register accessor: Ethernet MAC address1 low register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr1l::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr1l::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_addr1l`]
module"]
#[doc(alias = "MAC_ADDR1L")]
pub type MacAddr1l = crate::Reg<mac_addr1l::MacAddr1lSpec>;
#[doc = "Ethernet MAC address1 low register"]
pub mod mac_addr1l;
#[doc = "MAC_ADDR2H (rw) register accessor: Ethernet MAC address 2 high register (MAC_ADDR2H)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr2h::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr2h::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_addr2h`]
module"]
#[doc(alias = "MAC_ADDR2H")]
pub type MacAddr2h = crate::Reg<mac_addr2h::MacAddr2hSpec>;
#[doc = "Ethernet MAC address 2 high register (MAC_ADDR2H)"]
pub mod mac_addr2h;
#[doc = "MAC_ADDR2L (rw) register accessor: Ethernet MAC address 2 low register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr2l::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr2l::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_addr2l`]
module"]
#[doc(alias = "MAC_ADDR2L")]
pub type MacAddr2l = crate::Reg<mac_addr2l::MacAddr2lSpec>;
#[doc = "Ethernet MAC address 2 low register"]
pub mod mac_addr2l;
#[doc = "MAC_ADDR3H (rw) register accessor: Ethernet MAC address 3 high register (MAC_ADDR3H)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr3h::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr3h::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_addr3h`]
module"]
#[doc(alias = "MAC_ADDR3H")]
pub type MacAddr3h = crate::Reg<mac_addr3h::MacAddr3hSpec>;
#[doc = "Ethernet MAC address 3 high register (MAC_ADDR3H)"]
pub mod mac_addr3h;
#[doc = "MAC_ADDR3L (rw) register accessor: Ethernet MAC address 3 low register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_addr3l::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_addr3l::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mac_addr3l`]
module"]
#[doc(alias = "MAC_ADDR3L")]
pub type MacAddr3l = crate::Reg<mac_addr3l::MacAddr3lSpec>;
#[doc = "Ethernet MAC address 3 low register"]
pub mod mac_addr3l;
