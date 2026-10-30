#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    icache_ctrl: ICACHE_CTRL,
    icache_ctrl1: ICACHE_CTRL1,
    icache_tag_power_ctrl: ICACHE_TAG_POWER_CTRL,
    icache_prelock_ctrl: ICACHE_PRELOCK_CTRL,
    icache_prelock_sct0_addr: ICACHE_PRELOCK_SCT0_ADDR,
    icache_prelock_sct1_addr: ICACHE_PRELOCK_SCT1_ADDR,
    icache_prelock_sct_size: ICACHE_PRELOCK_SCT_SIZE,
    icache_lock_ctrl: ICACHE_LOCK_CTRL,
    icache_lock_addr: ICACHE_LOCK_ADDR,
    icache_lock_size: ICACHE_LOCK_SIZE,
    icache_sync_ctrl: ICACHE_SYNC_CTRL,
    icache_sync_addr: ICACHE_SYNC_ADDR,
    icache_sync_size: ICACHE_SYNC_SIZE,
    icache_preload_ctrl: ICACHE_PRELOAD_CTRL,
    icache_preload_addr: ICACHE_PRELOAD_ADDR,
    icache_preload_size: ICACHE_PRELOAD_SIZE,
    icache_autoload_ctrl: ICACHE_AUTOLOAD_CTRL,
    icache_autoload_sct0_addr: ICACHE_AUTOLOAD_SCT0_ADDR,
    icache_autoload_sct0_size: ICACHE_AUTOLOAD_SCT0_SIZE,
    icache_autoload_sct1_addr: ICACHE_AUTOLOAD_SCT1_ADDR,
    icache_autoload_sct1_size: ICACHE_AUTOLOAD_SCT1_SIZE,
    ibus_to_flash_start_vaddr: IBUS_TO_FLASH_START_VADDR,
    ibus_to_flash_end_vaddr: IBUS_TO_FLASH_END_VADDR,
    dbus_to_flash_start_vaddr: DBUS_TO_FLASH_START_VADDR,
    dbus_to_flash_end_vaddr: DBUS_TO_FLASH_END_VADDR,
    cache_acs_cnt_clr: CACHE_ACS_CNT_CLR,
    ibus_acs_miss_cnt: IBUS_ACS_MISS_CNT,
    ibus_acs_cnt: IBUS_ACS_CNT,
    dbus_acs_flash_miss_cnt: DBUS_ACS_FLASH_MISS_CNT,
    dbus_acs_cnt: DBUS_ACS_CNT,
    cache_ilg_int_ena: CACHE_ILG_INT_ENA,
    cache_ilg_int_clr: CACHE_ILG_INT_CLR,
    cache_ilg_int_st: CACHE_ILG_INT_ST,
    core0_acs_cache_int_ena: CORE0_ACS_CACHE_INT_ENA,
    core0_acs_cache_int_clr: CORE0_ACS_CACHE_INT_CLR,
    core0_acs_cache_int_st: CORE0_ACS_CACHE_INT_ST,
    core0_dbus_reject_st: CORE0_DBUS_REJECT_ST,
    core0_dbus_reject_vaddr: CORE0_DBUS_REJECT_VADDR,
    core0_ibus_reject_st: CORE0_IBUS_REJECT_ST,
    core0_ibus_reject_vaddr: CORE0_IBUS_REJECT_VADDR,
    cache_mmu_fault_content: CACHE_MMU_FAULT_CONTENT,
    cache_mmu_fault_vaddr: CACHE_MMU_FAULT_VADDR,
    cache_wrap_around_ctrl: CACHE_WRAP_AROUND_CTRL,
    cache_mmu_power_ctrl: CACHE_MMU_POWER_CTRL,
    cache_state: CACHE_STATE,
    cache_encrypt_decrypt_record_disable: CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE,
    cache_encrypt_decrypt_clk_force_on: CACHE_ENCRYPT_DECRYPT_CLK_FORCE_ON,
    cache_preload_int_ctrl: CACHE_PRELOAD_INT_CTRL,
    cache_sync_int_ctrl: CACHE_SYNC_INT_CTRL,
    cache_mmu_owner: CACHE_MMU_OWNER,
    cache_conf_misc: CACHE_CONF_MISC,
    icache_freeze: ICACHE_FREEZE,
    icache_atomic_operate_ena: ICACHE_ATOMIC_OPERATE_ENA,
    cache_request: CACHE_REQUEST,
    ibus_pms_tbl_lock: IBUS_PMS_TBL_LOCK,
    ibus_pms_tbl_boundary0: IBUS_PMS_TBL_BOUNDARY0,
    ibus_pms_tbl_boundary1: IBUS_PMS_TBL_BOUNDARY1,
    ibus_pms_tbl_boundary2: IBUS_PMS_TBL_BOUNDARY2,
    ibus_pms_tbl_attr: IBUS_PMS_TBL_ATTR,
    dbus_pms_tbl_lock: DBUS_PMS_TBL_LOCK,
    dbus_pms_tbl_boundary0: DBUS_PMS_TBL_BOUNDARY0,
    dbus_pms_tbl_boundary1: DBUS_PMS_TBL_BOUNDARY1,
    dbus_pms_tbl_boundary2: DBUS_PMS_TBL_BOUNDARY2,
    dbus_pms_tbl_attr: DBUS_PMS_TBL_ATTR,
    clock_gate: CLOCK_GATE,
    _reserved65: [u8; 0x02f8],
    reg_date: REG_DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_ctrl(&self) -> &ICACHE_CTRL {
        &self.icache_ctrl
    }
    #[doc = "0x04 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_ctrl1(&self) -> &ICACHE_CTRL1 {
        &self.icache_ctrl1
    }
    #[doc = "0x08 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_tag_power_ctrl(&self) -> &ICACHE_TAG_POWER_CTRL {
        &self.icache_tag_power_ctrl
    }
    #[doc = "0x0c - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_prelock_ctrl(&self) -> &ICACHE_PRELOCK_CTRL {
        &self.icache_prelock_ctrl
    }
    #[doc = "0x10 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_prelock_sct0_addr(&self) -> &ICACHE_PRELOCK_SCT0_ADDR {
        &self.icache_prelock_sct0_addr
    }
    #[doc = "0x14 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_prelock_sct1_addr(&self) -> &ICACHE_PRELOCK_SCT1_ADDR {
        &self.icache_prelock_sct1_addr
    }
    #[doc = "0x18 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_prelock_sct_size(&self) -> &ICACHE_PRELOCK_SCT_SIZE {
        &self.icache_prelock_sct_size
    }
    #[doc = "0x1c - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_lock_ctrl(&self) -> &ICACHE_LOCK_CTRL {
        &self.icache_lock_ctrl
    }
    #[doc = "0x20 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_lock_addr(&self) -> &ICACHE_LOCK_ADDR {
        &self.icache_lock_addr
    }
    #[doc = "0x24 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_lock_size(&self) -> &ICACHE_LOCK_SIZE {
        &self.icache_lock_size
    }
    #[doc = "0x28 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_sync_ctrl(&self) -> &ICACHE_SYNC_CTRL {
        &self.icache_sync_ctrl
    }
    #[doc = "0x2c - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_sync_addr(&self) -> &ICACHE_SYNC_ADDR {
        &self.icache_sync_addr
    }
    #[doc = "0x30 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_sync_size(&self) -> &ICACHE_SYNC_SIZE {
        &self.icache_sync_size
    }
    #[doc = "0x34 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_preload_ctrl(&self) -> &ICACHE_PRELOAD_CTRL {
        &self.icache_preload_ctrl
    }
    #[doc = "0x38 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_preload_addr(&self) -> &ICACHE_PRELOAD_ADDR {
        &self.icache_preload_addr
    }
    #[doc = "0x3c - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_preload_size(&self) -> &ICACHE_PRELOAD_SIZE {
        &self.icache_preload_size
    }
    #[doc = "0x40 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_autoload_ctrl(&self) -> &ICACHE_AUTOLOAD_CTRL {
        &self.icache_autoload_ctrl
    }
    #[doc = "0x44 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_autoload_sct0_addr(&self) -> &ICACHE_AUTOLOAD_SCT0_ADDR {
        &self.icache_autoload_sct0_addr
    }
    #[doc = "0x48 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_autoload_sct0_size(&self) -> &ICACHE_AUTOLOAD_SCT0_SIZE {
        &self.icache_autoload_sct0_size
    }
    #[doc = "0x4c - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_autoload_sct1_addr(&self) -> &ICACHE_AUTOLOAD_SCT1_ADDR {
        &self.icache_autoload_sct1_addr
    }
    #[doc = "0x50 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_autoload_sct1_size(&self) -> &ICACHE_AUTOLOAD_SCT1_SIZE {
        &self.icache_autoload_sct1_size
    }
    #[doc = "0x54 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn ibus_to_flash_start_vaddr(&self) -> &IBUS_TO_FLASH_START_VADDR {
        &self.ibus_to_flash_start_vaddr
    }
    #[doc = "0x58 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn ibus_to_flash_end_vaddr(&self) -> &IBUS_TO_FLASH_END_VADDR {
        &self.ibus_to_flash_end_vaddr
    }
    #[doc = "0x5c - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn dbus_to_flash_start_vaddr(&self) -> &DBUS_TO_FLASH_START_VADDR {
        &self.dbus_to_flash_start_vaddr
    }
    #[doc = "0x60 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn dbus_to_flash_end_vaddr(&self) -> &DBUS_TO_FLASH_END_VADDR {
        &self.dbus_to_flash_end_vaddr
    }
    #[doc = "0x64 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_acs_cnt_clr(&self) -> &CACHE_ACS_CNT_CLR {
        &self.cache_acs_cnt_clr
    }
    #[doc = "0x68 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn ibus_acs_miss_cnt(&self) -> &IBUS_ACS_MISS_CNT {
        &self.ibus_acs_miss_cnt
    }
    #[doc = "0x6c - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn ibus_acs_cnt(&self) -> &IBUS_ACS_CNT {
        &self.ibus_acs_cnt
    }
    #[doc = "0x70 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn dbus_acs_flash_miss_cnt(&self) -> &DBUS_ACS_FLASH_MISS_CNT {
        &self.dbus_acs_flash_miss_cnt
    }
    #[doc = "0x74 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn dbus_acs_cnt(&self) -> &DBUS_ACS_CNT {
        &self.dbus_acs_cnt
    }
    #[doc = "0x78 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_ilg_int_ena(&self) -> &CACHE_ILG_INT_ENA {
        &self.cache_ilg_int_ena
    }
    #[doc = "0x7c - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_ilg_int_clr(&self) -> &CACHE_ILG_INT_CLR {
        &self.cache_ilg_int_clr
    }
    #[doc = "0x80 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_ilg_int_st(&self) -> &CACHE_ILG_INT_ST {
        &self.cache_ilg_int_st
    }
    #[doc = "0x84 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn core0_acs_cache_int_ena(&self) -> &CORE0_ACS_CACHE_INT_ENA {
        &self.core0_acs_cache_int_ena
    }
    #[doc = "0x88 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn core0_acs_cache_int_clr(&self) -> &CORE0_ACS_CACHE_INT_CLR {
        &self.core0_acs_cache_int_clr
    }
    #[doc = "0x8c - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn core0_acs_cache_int_st(&self) -> &CORE0_ACS_CACHE_INT_ST {
        &self.core0_acs_cache_int_st
    }
    #[doc = "0x90 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn core0_dbus_reject_st(&self) -> &CORE0_DBUS_REJECT_ST {
        &self.core0_dbus_reject_st
    }
    #[doc = "0x94 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn core0_dbus_reject_vaddr(&self) -> &CORE0_DBUS_REJECT_VADDR {
        &self.core0_dbus_reject_vaddr
    }
    #[doc = "0x98 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn core0_ibus_reject_st(&self) -> &CORE0_IBUS_REJECT_ST {
        &self.core0_ibus_reject_st
    }
    #[doc = "0x9c - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn core0_ibus_reject_vaddr(&self) -> &CORE0_IBUS_REJECT_VADDR {
        &self.core0_ibus_reject_vaddr
    }
    #[doc = "0xa0 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_mmu_fault_content(&self) -> &CACHE_MMU_FAULT_CONTENT {
        &self.cache_mmu_fault_content
    }
    #[doc = "0xa4 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_mmu_fault_vaddr(&self) -> &CACHE_MMU_FAULT_VADDR {
        &self.cache_mmu_fault_vaddr
    }
    #[doc = "0xa8 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_wrap_around_ctrl(&self) -> &CACHE_WRAP_AROUND_CTRL {
        &self.cache_wrap_around_ctrl
    }
    #[doc = "0xac - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_mmu_power_ctrl(&self) -> &CACHE_MMU_POWER_CTRL {
        &self.cache_mmu_power_ctrl
    }
    #[doc = "0xb0 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_state(&self) -> &CACHE_STATE {
        &self.cache_state
    }
    #[doc = "0xb4 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_encrypt_decrypt_record_disable(
        &self,
    ) -> &CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE {
        &self.cache_encrypt_decrypt_record_disable
    }
    #[doc = "0xb8 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_encrypt_decrypt_clk_force_on(&self) -> &CACHE_ENCRYPT_DECRYPT_CLK_FORCE_ON {
        &self.cache_encrypt_decrypt_clk_force_on
    }
    #[doc = "0xbc - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_preload_int_ctrl(&self) -> &CACHE_PRELOAD_INT_CTRL {
        &self.cache_preload_int_ctrl
    }
    #[doc = "0xc0 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_sync_int_ctrl(&self) -> &CACHE_SYNC_INT_CTRL {
        &self.cache_sync_int_ctrl
    }
    #[doc = "0xc4 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_mmu_owner(&self) -> &CACHE_MMU_OWNER {
        &self.cache_mmu_owner
    }
    #[doc = "0xc8 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_conf_misc(&self) -> &CACHE_CONF_MISC {
        &self.cache_conf_misc
    }
    #[doc = "0xcc - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_freeze(&self) -> &ICACHE_FREEZE {
        &self.icache_freeze
    }
    #[doc = "0xd0 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn icache_atomic_operate_ena(&self) -> &ICACHE_ATOMIC_OPERATE_ENA {
        &self.icache_atomic_operate_ena
    }
    #[doc = "0xd4 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn cache_request(&self) -> &CACHE_REQUEST {
        &self.cache_request
    }
    #[doc = "0xd8 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn ibus_pms_tbl_lock(&self) -> &IBUS_PMS_TBL_LOCK {
        &self.ibus_pms_tbl_lock
    }
    #[doc = "0xdc - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn ibus_pms_tbl_boundary0(&self) -> &IBUS_PMS_TBL_BOUNDARY0 {
        &self.ibus_pms_tbl_boundary0
    }
    #[doc = "0xe0 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn ibus_pms_tbl_boundary1(&self) -> &IBUS_PMS_TBL_BOUNDARY1 {
        &self.ibus_pms_tbl_boundary1
    }
    #[doc = "0xe4 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn ibus_pms_tbl_boundary2(&self) -> &IBUS_PMS_TBL_BOUNDARY2 {
        &self.ibus_pms_tbl_boundary2
    }
    #[doc = "0xe8 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn ibus_pms_tbl_attr(&self) -> &IBUS_PMS_TBL_ATTR {
        &self.ibus_pms_tbl_attr
    }
    #[doc = "0xec - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn dbus_pms_tbl_lock(&self) -> &DBUS_PMS_TBL_LOCK {
        &self.dbus_pms_tbl_lock
    }
    #[doc = "0xf0 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn dbus_pms_tbl_boundary0(&self) -> &DBUS_PMS_TBL_BOUNDARY0 {
        &self.dbus_pms_tbl_boundary0
    }
    #[doc = "0xf4 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn dbus_pms_tbl_boundary1(&self) -> &DBUS_PMS_TBL_BOUNDARY1 {
        &self.dbus_pms_tbl_boundary1
    }
    #[doc = "0xf8 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn dbus_pms_tbl_boundary2(&self) -> &DBUS_PMS_TBL_BOUNDARY2 {
        &self.dbus_pms_tbl_boundary2
    }
    #[doc = "0xfc - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn dbus_pms_tbl_attr(&self) -> &DBUS_PMS_TBL_ATTR {
        &self.dbus_pms_tbl_attr
    }
    #[doc = "0x100 - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn clock_gate(&self) -> &CLOCK_GATE {
        &self.clock_gate
    }
    #[doc = "0x3fc - This description will be updated in the near future."]
    #[inline(always)]
    pub const fn reg_date(&self) -> &REG_DATE {
        &self.reg_date
    }
}
#[doc = "ICACHE_CTRL (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_ctrl`] module"]
pub type ICACHE_CTRL = crate::Reg<icache_ctrl::ICACHE_CTRL_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_ctrl;
#[doc = "ICACHE_CTRL1 (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_ctrl1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_ctrl1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_ctrl1`] module"]
pub type ICACHE_CTRL1 = crate::Reg<icache_ctrl1::ICACHE_CTRL1_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_ctrl1;
#[doc = "ICACHE_TAG_POWER_CTRL (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_tag_power_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_tag_power_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_tag_power_ctrl`] module"]
pub type ICACHE_TAG_POWER_CTRL = crate::Reg<icache_tag_power_ctrl::ICACHE_TAG_POWER_CTRL_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_tag_power_ctrl;
#[doc = "ICACHE_PRELOCK_CTRL (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_prelock_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_prelock_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_prelock_ctrl`] module"]
pub type ICACHE_PRELOCK_CTRL = crate::Reg<icache_prelock_ctrl::ICACHE_PRELOCK_CTRL_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_prelock_ctrl;
#[doc = "ICACHE_PRELOCK_SCT0_ADDR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_prelock_sct0_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_prelock_sct0_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_prelock_sct0_addr`] module"]
pub type ICACHE_PRELOCK_SCT0_ADDR =
    crate::Reg<icache_prelock_sct0_addr::ICACHE_PRELOCK_SCT0_ADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_prelock_sct0_addr;
#[doc = "ICACHE_PRELOCK_SCT1_ADDR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_prelock_sct1_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_prelock_sct1_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_prelock_sct1_addr`] module"]
pub type ICACHE_PRELOCK_SCT1_ADDR =
    crate::Reg<icache_prelock_sct1_addr::ICACHE_PRELOCK_SCT1_ADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_prelock_sct1_addr;
#[doc = "ICACHE_PRELOCK_SCT_SIZE (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_prelock_sct_size::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_prelock_sct_size::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_prelock_sct_size`] module"]
pub type ICACHE_PRELOCK_SCT_SIZE =
    crate::Reg<icache_prelock_sct_size::ICACHE_PRELOCK_SCT_SIZE_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_prelock_sct_size;
#[doc = "ICACHE_LOCK_CTRL (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_lock_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_lock_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_lock_ctrl`] module"]
pub type ICACHE_LOCK_CTRL = crate::Reg<icache_lock_ctrl::ICACHE_LOCK_CTRL_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_lock_ctrl;
#[doc = "ICACHE_LOCK_ADDR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_lock_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_lock_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_lock_addr`] module"]
pub type ICACHE_LOCK_ADDR = crate::Reg<icache_lock_addr::ICACHE_LOCK_ADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_lock_addr;
#[doc = "ICACHE_LOCK_SIZE (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_lock_size::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_lock_size::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_lock_size`] module"]
pub type ICACHE_LOCK_SIZE = crate::Reg<icache_lock_size::ICACHE_LOCK_SIZE_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_lock_size;
#[doc = "ICACHE_SYNC_CTRL (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_sync_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_sync_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_sync_ctrl`] module"]
pub type ICACHE_SYNC_CTRL = crate::Reg<icache_sync_ctrl::ICACHE_SYNC_CTRL_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_sync_ctrl;
#[doc = "ICACHE_SYNC_ADDR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_sync_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_sync_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_sync_addr`] module"]
pub type ICACHE_SYNC_ADDR = crate::Reg<icache_sync_addr::ICACHE_SYNC_ADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_sync_addr;
#[doc = "ICACHE_SYNC_SIZE (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_sync_size::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_sync_size::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_sync_size`] module"]
pub type ICACHE_SYNC_SIZE = crate::Reg<icache_sync_size::ICACHE_SYNC_SIZE_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_sync_size;
#[doc = "ICACHE_PRELOAD_CTRL (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_preload_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_preload_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_preload_ctrl`] module"]
pub type ICACHE_PRELOAD_CTRL = crate::Reg<icache_preload_ctrl::ICACHE_PRELOAD_CTRL_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_preload_ctrl;
#[doc = "ICACHE_PRELOAD_ADDR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_preload_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_preload_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_preload_addr`] module"]
pub type ICACHE_PRELOAD_ADDR = crate::Reg<icache_preload_addr::ICACHE_PRELOAD_ADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_preload_addr;
#[doc = "ICACHE_PRELOAD_SIZE (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_preload_size::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_preload_size::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_preload_size`] module"]
pub type ICACHE_PRELOAD_SIZE = crate::Reg<icache_preload_size::ICACHE_PRELOAD_SIZE_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_preload_size;
#[doc = "ICACHE_AUTOLOAD_CTRL (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_autoload_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_autoload_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_autoload_ctrl`] module"]
pub type ICACHE_AUTOLOAD_CTRL = crate::Reg<icache_autoload_ctrl::ICACHE_AUTOLOAD_CTRL_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_autoload_ctrl;
#[doc = "ICACHE_AUTOLOAD_SCT0_ADDR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_autoload_sct0_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_autoload_sct0_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_autoload_sct0_addr`] module"]
pub type ICACHE_AUTOLOAD_SCT0_ADDR =
    crate::Reg<icache_autoload_sct0_addr::ICACHE_AUTOLOAD_SCT0_ADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_autoload_sct0_addr;
#[doc = "ICACHE_AUTOLOAD_SCT0_SIZE (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_autoload_sct0_size::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_autoload_sct0_size::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_autoload_sct0_size`] module"]
pub type ICACHE_AUTOLOAD_SCT0_SIZE =
    crate::Reg<icache_autoload_sct0_size::ICACHE_AUTOLOAD_SCT0_SIZE_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_autoload_sct0_size;
#[doc = "ICACHE_AUTOLOAD_SCT1_ADDR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_autoload_sct1_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_autoload_sct1_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_autoload_sct1_addr`] module"]
pub type ICACHE_AUTOLOAD_SCT1_ADDR =
    crate::Reg<icache_autoload_sct1_addr::ICACHE_AUTOLOAD_SCT1_ADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_autoload_sct1_addr;
#[doc = "ICACHE_AUTOLOAD_SCT1_SIZE (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_autoload_sct1_size::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_autoload_sct1_size::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_autoload_sct1_size`] module"]
pub type ICACHE_AUTOLOAD_SCT1_SIZE =
    crate::Reg<icache_autoload_sct1_size::ICACHE_AUTOLOAD_SCT1_SIZE_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_autoload_sct1_size;
#[doc = "IBUS_TO_FLASH_START_VADDR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`ibus_to_flash_start_vaddr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ibus_to_flash_start_vaddr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ibus_to_flash_start_vaddr`] module"]
pub type IBUS_TO_FLASH_START_VADDR =
    crate::Reg<ibus_to_flash_start_vaddr::IBUS_TO_FLASH_START_VADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod ibus_to_flash_start_vaddr;
#[doc = "IBUS_TO_FLASH_END_VADDR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`ibus_to_flash_end_vaddr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ibus_to_flash_end_vaddr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ibus_to_flash_end_vaddr`] module"]
pub type IBUS_TO_FLASH_END_VADDR =
    crate::Reg<ibus_to_flash_end_vaddr::IBUS_TO_FLASH_END_VADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod ibus_to_flash_end_vaddr;
#[doc = "DBUS_TO_FLASH_START_VADDR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`dbus_to_flash_start_vaddr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dbus_to_flash_start_vaddr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dbus_to_flash_start_vaddr`] module"]
pub type DBUS_TO_FLASH_START_VADDR =
    crate::Reg<dbus_to_flash_start_vaddr::DBUS_TO_FLASH_START_VADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod dbus_to_flash_start_vaddr;
#[doc = "DBUS_TO_FLASH_END_VADDR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`dbus_to_flash_end_vaddr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dbus_to_flash_end_vaddr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dbus_to_flash_end_vaddr`] module"]
pub type DBUS_TO_FLASH_END_VADDR =
    crate::Reg<dbus_to_flash_end_vaddr::DBUS_TO_FLASH_END_VADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod dbus_to_flash_end_vaddr;
#[doc = "CACHE_ACS_CNT_CLR (w) register accessor: This description will be updated in the near future.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_acs_cnt_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_acs_cnt_clr`] module"]
pub type CACHE_ACS_CNT_CLR = crate::Reg<cache_acs_cnt_clr::CACHE_ACS_CNT_CLR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_acs_cnt_clr;
#[doc = "IBUS_ACS_MISS_CNT (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`ibus_acs_miss_cnt::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ibus_acs_miss_cnt`] module"]
pub type IBUS_ACS_MISS_CNT = crate::Reg<ibus_acs_miss_cnt::IBUS_ACS_MISS_CNT_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod ibus_acs_miss_cnt;
#[doc = "IBUS_ACS_CNT (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`ibus_acs_cnt::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ibus_acs_cnt`] module"]
pub type IBUS_ACS_CNT = crate::Reg<ibus_acs_cnt::IBUS_ACS_CNT_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod ibus_acs_cnt;
#[doc = "DBUS_ACS_FLASH_MISS_CNT (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`dbus_acs_flash_miss_cnt::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dbus_acs_flash_miss_cnt`] module"]
pub type DBUS_ACS_FLASH_MISS_CNT =
    crate::Reg<dbus_acs_flash_miss_cnt::DBUS_ACS_FLASH_MISS_CNT_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod dbus_acs_flash_miss_cnt;
#[doc = "DBUS_ACS_CNT (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`dbus_acs_cnt::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dbus_acs_cnt`] module"]
pub type DBUS_ACS_CNT = crate::Reg<dbus_acs_cnt::DBUS_ACS_CNT_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod dbus_acs_cnt;
#[doc = "CACHE_ILG_INT_ENA (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_ilg_int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_ilg_int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_ilg_int_ena`] module"]
pub type CACHE_ILG_INT_ENA = crate::Reg<cache_ilg_int_ena::CACHE_ILG_INT_ENA_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_ilg_int_ena;
#[doc = "CACHE_ILG_INT_CLR (w) register accessor: This description will be updated in the near future.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_ilg_int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_ilg_int_clr`] module"]
pub type CACHE_ILG_INT_CLR = crate::Reg<cache_ilg_int_clr::CACHE_ILG_INT_CLR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_ilg_int_clr;
#[doc = "CACHE_ILG_INT_ST (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_ilg_int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_ilg_int_st`] module"]
pub type CACHE_ILG_INT_ST = crate::Reg<cache_ilg_int_st::CACHE_ILG_INT_ST_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_ilg_int_st;
#[doc = "CORE0_ACS_CACHE_INT_ENA (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`core0_acs_cache_int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core0_acs_cache_int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core0_acs_cache_int_ena`] module"]
pub type CORE0_ACS_CACHE_INT_ENA =
    crate::Reg<core0_acs_cache_int_ena::CORE0_ACS_CACHE_INT_ENA_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod core0_acs_cache_int_ena;
#[doc = "CORE0_ACS_CACHE_INT_CLR (w) register accessor: This description will be updated in the near future.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core0_acs_cache_int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core0_acs_cache_int_clr`] module"]
pub type CORE0_ACS_CACHE_INT_CLR =
    crate::Reg<core0_acs_cache_int_clr::CORE0_ACS_CACHE_INT_CLR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod core0_acs_cache_int_clr;
#[doc = "CORE0_ACS_CACHE_INT_ST (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`core0_acs_cache_int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core0_acs_cache_int_st`] module"]
pub type CORE0_ACS_CACHE_INT_ST = crate::Reg<core0_acs_cache_int_st::CORE0_ACS_CACHE_INT_ST_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod core0_acs_cache_int_st;
#[doc = "CORE0_DBUS_REJECT_ST (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`core0_dbus_reject_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core0_dbus_reject_st`] module"]
pub type CORE0_DBUS_REJECT_ST = crate::Reg<core0_dbus_reject_st::CORE0_DBUS_REJECT_ST_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod core0_dbus_reject_st;
#[doc = "CORE0_DBUS_REJECT_VADDR (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`core0_dbus_reject_vaddr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core0_dbus_reject_vaddr`] module"]
pub type CORE0_DBUS_REJECT_VADDR =
    crate::Reg<core0_dbus_reject_vaddr::CORE0_DBUS_REJECT_VADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod core0_dbus_reject_vaddr;
#[doc = "CORE0_IBUS_REJECT_ST (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`core0_ibus_reject_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core0_ibus_reject_st`] module"]
pub type CORE0_IBUS_REJECT_ST = crate::Reg<core0_ibus_reject_st::CORE0_IBUS_REJECT_ST_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod core0_ibus_reject_st;
#[doc = "CORE0_IBUS_REJECT_VADDR (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`core0_ibus_reject_vaddr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core0_ibus_reject_vaddr`] module"]
pub type CORE0_IBUS_REJECT_VADDR =
    crate::Reg<core0_ibus_reject_vaddr::CORE0_IBUS_REJECT_VADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod core0_ibus_reject_vaddr;
#[doc = "CACHE_MMU_FAULT_CONTENT (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_mmu_fault_content::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_mmu_fault_content`] module"]
pub type CACHE_MMU_FAULT_CONTENT =
    crate::Reg<cache_mmu_fault_content::CACHE_MMU_FAULT_CONTENT_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_mmu_fault_content;
#[doc = "CACHE_MMU_FAULT_VADDR (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_mmu_fault_vaddr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_mmu_fault_vaddr`] module"]
pub type CACHE_MMU_FAULT_VADDR = crate::Reg<cache_mmu_fault_vaddr::CACHE_MMU_FAULT_VADDR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_mmu_fault_vaddr;
#[doc = "CACHE_WRAP_AROUND_CTRL (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_wrap_around_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_wrap_around_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_wrap_around_ctrl`] module"]
pub type CACHE_WRAP_AROUND_CTRL = crate::Reg<cache_wrap_around_ctrl::CACHE_WRAP_AROUND_CTRL_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_wrap_around_ctrl;
#[doc = "CACHE_MMU_POWER_CTRL (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_mmu_power_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_mmu_power_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_mmu_power_ctrl`] module"]
pub type CACHE_MMU_POWER_CTRL = crate::Reg<cache_mmu_power_ctrl::CACHE_MMU_POWER_CTRL_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_mmu_power_ctrl;
#[doc = "CACHE_STATE (r) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_state::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_state`] module"]
pub type CACHE_STATE = crate::Reg<cache_state::CACHE_STATE_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_state;
#[doc = "CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_encrypt_decrypt_record_disable::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_encrypt_decrypt_record_disable::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_encrypt_decrypt_record_disable`] module"]
pub type CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE =
    crate::Reg<cache_encrypt_decrypt_record_disable::CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_encrypt_decrypt_record_disable;
#[doc = "CACHE_ENCRYPT_DECRYPT_CLK_FORCE_ON (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_encrypt_decrypt_clk_force_on::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_encrypt_decrypt_clk_force_on::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_encrypt_decrypt_clk_force_on`] module"]
pub type CACHE_ENCRYPT_DECRYPT_CLK_FORCE_ON =
    crate::Reg<cache_encrypt_decrypt_clk_force_on::CACHE_ENCRYPT_DECRYPT_CLK_FORCE_ON_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_encrypt_decrypt_clk_force_on;
#[doc = "CACHE_PRELOAD_INT_CTRL (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_preload_int_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_preload_int_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_preload_int_ctrl`] module"]
pub type CACHE_PRELOAD_INT_CTRL = crate::Reg<cache_preload_int_ctrl::CACHE_PRELOAD_INT_CTRL_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_preload_int_ctrl;
#[doc = "CACHE_SYNC_INT_CTRL (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_sync_int_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_sync_int_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_sync_int_ctrl`] module"]
pub type CACHE_SYNC_INT_CTRL = crate::Reg<cache_sync_int_ctrl::CACHE_SYNC_INT_CTRL_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_sync_int_ctrl;
#[doc = "CACHE_MMU_OWNER (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_mmu_owner::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_mmu_owner::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_mmu_owner`] module"]
pub type CACHE_MMU_OWNER = crate::Reg<cache_mmu_owner::CACHE_MMU_OWNER_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_mmu_owner;
#[doc = "CACHE_CONF_MISC (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_conf_misc::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_conf_misc::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_conf_misc`] module"]
pub type CACHE_CONF_MISC = crate::Reg<cache_conf_misc::CACHE_CONF_MISC_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_conf_misc;
#[doc = "ICACHE_FREEZE (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_freeze::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_freeze::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_freeze`] module"]
pub type ICACHE_FREEZE = crate::Reg<icache_freeze::ICACHE_FREEZE_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_freeze;
#[doc = "ICACHE_ATOMIC_OPERATE_ENA (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_atomic_operate_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_atomic_operate_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@icache_atomic_operate_ena`] module"]
pub type ICACHE_ATOMIC_OPERATE_ENA =
    crate::Reg<icache_atomic_operate_ena::ICACHE_ATOMIC_OPERATE_ENA_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod icache_atomic_operate_ena;
#[doc = "CACHE_REQUEST (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_request::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_request::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_request`] module"]
pub type CACHE_REQUEST = crate::Reg<cache_request::CACHE_REQUEST_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod cache_request;
#[doc = "IBUS_PMS_TBL_LOCK (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`ibus_pms_tbl_lock::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ibus_pms_tbl_lock::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ibus_pms_tbl_lock`] module"]
pub type IBUS_PMS_TBL_LOCK = crate::Reg<ibus_pms_tbl_lock::IBUS_PMS_TBL_LOCK_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod ibus_pms_tbl_lock;
#[doc = "IBUS_PMS_TBL_BOUNDARY0 (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`ibus_pms_tbl_boundary0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ibus_pms_tbl_boundary0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ibus_pms_tbl_boundary0`] module"]
pub type IBUS_PMS_TBL_BOUNDARY0 = crate::Reg<ibus_pms_tbl_boundary0::IBUS_PMS_TBL_BOUNDARY0_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod ibus_pms_tbl_boundary0;
#[doc = "IBUS_PMS_TBL_BOUNDARY1 (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`ibus_pms_tbl_boundary1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ibus_pms_tbl_boundary1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ibus_pms_tbl_boundary1`] module"]
pub type IBUS_PMS_TBL_BOUNDARY1 = crate::Reg<ibus_pms_tbl_boundary1::IBUS_PMS_TBL_BOUNDARY1_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod ibus_pms_tbl_boundary1;
#[doc = "IBUS_PMS_TBL_BOUNDARY2 (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`ibus_pms_tbl_boundary2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ibus_pms_tbl_boundary2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ibus_pms_tbl_boundary2`] module"]
pub type IBUS_PMS_TBL_BOUNDARY2 = crate::Reg<ibus_pms_tbl_boundary2::IBUS_PMS_TBL_BOUNDARY2_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod ibus_pms_tbl_boundary2;
#[doc = "IBUS_PMS_TBL_ATTR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`ibus_pms_tbl_attr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ibus_pms_tbl_attr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ibus_pms_tbl_attr`] module"]
pub type IBUS_PMS_TBL_ATTR = crate::Reg<ibus_pms_tbl_attr::IBUS_PMS_TBL_ATTR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod ibus_pms_tbl_attr;
#[doc = "DBUS_PMS_TBL_LOCK (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`dbus_pms_tbl_lock::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dbus_pms_tbl_lock::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dbus_pms_tbl_lock`] module"]
pub type DBUS_PMS_TBL_LOCK = crate::Reg<dbus_pms_tbl_lock::DBUS_PMS_TBL_LOCK_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod dbus_pms_tbl_lock;
#[doc = "DBUS_PMS_TBL_BOUNDARY0 (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`dbus_pms_tbl_boundary0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dbus_pms_tbl_boundary0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dbus_pms_tbl_boundary0`] module"]
pub type DBUS_PMS_TBL_BOUNDARY0 = crate::Reg<dbus_pms_tbl_boundary0::DBUS_PMS_TBL_BOUNDARY0_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod dbus_pms_tbl_boundary0;
#[doc = "DBUS_PMS_TBL_BOUNDARY1 (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`dbus_pms_tbl_boundary1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dbus_pms_tbl_boundary1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dbus_pms_tbl_boundary1`] module"]
pub type DBUS_PMS_TBL_BOUNDARY1 = crate::Reg<dbus_pms_tbl_boundary1::DBUS_PMS_TBL_BOUNDARY1_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod dbus_pms_tbl_boundary1;
#[doc = "DBUS_PMS_TBL_BOUNDARY2 (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`dbus_pms_tbl_boundary2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dbus_pms_tbl_boundary2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dbus_pms_tbl_boundary2`] module"]
pub type DBUS_PMS_TBL_BOUNDARY2 = crate::Reg<dbus_pms_tbl_boundary2::DBUS_PMS_TBL_BOUNDARY2_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod dbus_pms_tbl_boundary2;
#[doc = "DBUS_PMS_TBL_ATTR (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`dbus_pms_tbl_attr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dbus_pms_tbl_attr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dbus_pms_tbl_attr`] module"]
pub type DBUS_PMS_TBL_ATTR = crate::Reg<dbus_pms_tbl_attr::DBUS_PMS_TBL_ATTR_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod dbus_pms_tbl_attr;
#[doc = "CLOCK_GATE (rw) register accessor: This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`clock_gate::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clock_gate::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clock_gate`] module"]
pub type CLOCK_GATE = crate::Reg<clock_gate::CLOCK_GATE_SPEC>;
#[doc = "This description will be updated in the near future."]
pub mod clock_gate;
pub use crate::aes::{date as reg_date, DATE as REG_DATE};
