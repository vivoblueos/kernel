#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    external_device_encrypt_decrypt_control: EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL,
    sram_usage_conf: SRAM_USAGE_CONF,
    sec_dpa_conf: SEC_DPA_CONF,
    cpu_peri_timeout_conf: CPU_PERI_TIMEOUT_CONF,
    cpu_peri_timeout_addr: CPU_PERI_TIMEOUT_ADDR,
    cpu_peri_timeout_uid: CPU_PERI_TIMEOUT_UID,
    hp_peri_timeout_conf: HP_PERI_TIMEOUT_CONF,
    hp_peri_timeout_addr: HP_PERI_TIMEOUT_ADDR,
    hp_peri_timeout_uid: HP_PERI_TIMEOUT_UID,
    modem_peri_timeout_conf: MODEM_PERI_TIMEOUT_CONF,
    modem_peri_timeout_addr: MODEM_PERI_TIMEOUT_ADDR,
    modem_peri_timeout_uid: MODEM_PERI_TIMEOUT_UID,
    sdio_ctrl: SDIO_CTRL,
    retention_conf: RETENTION_CONF,
    rom_table_lock: ROM_TABLE_LOCK,
    rom_table: ROM_TABLE,
    core_debug_runstall_conf: CORE_DEBUG_RUNSTALL_CONF,
    mem_test_conf: MEM_TEST_CONF,
    _reserved18: [u8; 0x0398],
    rnd_eco: RND_ECO,
    rnd_eco_low: RND_ECO_LOW,
    rnd_eco_high: RND_ECO_HIGH,
    _reserved21: [u8; 0x0c],
    clock_gate: CLOCK_GATE,
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - EXTERNAL DEVICE ENCRYPTION/DECRYPTION configuration register"]
    #[inline(always)]
    pub const fn external_device_encrypt_decrypt_control(
        &self,
    ) -> &EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL {
        &self.external_device_encrypt_decrypt_control
    }
    #[doc = "0x04 - HP memory usage configuration register"]
    #[inline(always)]
    pub const fn sram_usage_conf(&self) -> &SRAM_USAGE_CONF {
        &self.sram_usage_conf
    }
    #[doc = "0x08 - HP anti-DPA security configuration register"]
    #[inline(always)]
    pub const fn sec_dpa_conf(&self) -> &SEC_DPA_CONF {
        &self.sec_dpa_conf
    }
    #[doc = "0x0c - CPU_PERI_TIMEOUT configuration register"]
    #[inline(always)]
    pub const fn cpu_peri_timeout_conf(&self) -> &CPU_PERI_TIMEOUT_CONF {
        &self.cpu_peri_timeout_conf
    }
    #[doc = "0x10 - CPU_PERI_TIMEOUT_ADDR register"]
    #[inline(always)]
    pub const fn cpu_peri_timeout_addr(&self) -> &CPU_PERI_TIMEOUT_ADDR {
        &self.cpu_peri_timeout_addr
    }
    #[doc = "0x14 - CPU_PERI_TIMEOUT_UID register"]
    #[inline(always)]
    pub const fn cpu_peri_timeout_uid(&self) -> &CPU_PERI_TIMEOUT_UID {
        &self.cpu_peri_timeout_uid
    }
    #[doc = "0x18 - HP_PERI_TIMEOUT configuration register"]
    #[inline(always)]
    pub const fn hp_peri_timeout_conf(&self) -> &HP_PERI_TIMEOUT_CONF {
        &self.hp_peri_timeout_conf
    }
    #[doc = "0x1c - HP_PERI_TIMEOUT_ADDR register"]
    #[inline(always)]
    pub const fn hp_peri_timeout_addr(&self) -> &HP_PERI_TIMEOUT_ADDR {
        &self.hp_peri_timeout_addr
    }
    #[doc = "0x20 - HP_PERI_TIMEOUT_UID register"]
    #[inline(always)]
    pub const fn hp_peri_timeout_uid(&self) -> &HP_PERI_TIMEOUT_UID {
        &self.hp_peri_timeout_uid
    }
    #[doc = "0x24 - MODEM_PERI_TIMEOUT configuration register"]
    #[inline(always)]
    pub const fn modem_peri_timeout_conf(&self) -> &MODEM_PERI_TIMEOUT_CONF {
        &self.modem_peri_timeout_conf
    }
    #[doc = "0x28 - MODEM_PERI_TIMEOUT_ADDR register"]
    #[inline(always)]
    pub const fn modem_peri_timeout_addr(&self) -> &MODEM_PERI_TIMEOUT_ADDR {
        &self.modem_peri_timeout_addr
    }
    #[doc = "0x2c - MODEM_PERI_TIMEOUT_UID register"]
    #[inline(always)]
    pub const fn modem_peri_timeout_uid(&self) -> &MODEM_PERI_TIMEOUT_UID {
        &self.modem_peri_timeout_uid
    }
    #[doc = "0x30 - SDIO Control configuration register"]
    #[inline(always)]
    pub const fn sdio_ctrl(&self) -> &SDIO_CTRL {
        &self.sdio_ctrl
    }
    #[doc = "0x34 - Retention configuration register"]
    #[inline(always)]
    pub const fn retention_conf(&self) -> &RETENTION_CONF {
        &self.retention_conf
    }
    #[doc = "0x38 - Rom-Table lock register"]
    #[inline(always)]
    pub const fn rom_table_lock(&self) -> &ROM_TABLE_LOCK {
        &self.rom_table_lock
    }
    #[doc = "0x3c - Rom-Table register"]
    #[inline(always)]
    pub const fn rom_table(&self) -> &ROM_TABLE {
        &self.rom_table
    }
    #[doc = "0x40 - Core Debug runstall configure register"]
    #[inline(always)]
    pub const fn core_debug_runstall_conf(&self) -> &CORE_DEBUG_RUNSTALL_CONF {
        &self.core_debug_runstall_conf
    }
    #[doc = "0x44 - MEM_TEST configuration register"]
    #[inline(always)]
    pub const fn mem_test_conf(&self) -> &MEM_TEST_CONF {
        &self.mem_test_conf
    }
    #[doc = "0x3e0 - redcy eco register."]
    #[inline(always)]
    pub const fn rnd_eco(&self) -> &RND_ECO {
        &self.rnd_eco
    }
    #[doc = "0x3e4 - redcy eco low register."]
    #[inline(always)]
    pub const fn rnd_eco_low(&self) -> &RND_ECO_LOW {
        &self.rnd_eco_low
    }
    #[doc = "0x3e8 - redcy eco high register."]
    #[inline(always)]
    pub const fn rnd_eco_high(&self) -> &RND_ECO_HIGH {
        &self.rnd_eco_high
    }
    #[doc = "0x3f8 - HP-SYSTEM clock gating configure register"]
    #[inline(always)]
    pub const fn clock_gate(&self) -> &CLOCK_GATE {
        &self.clock_gate
    }
    #[doc = "0x3fc - Date register."]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL (rw) register accessor: EXTERNAL DEVICE ENCRYPTION/DECRYPTION configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`external_device_encrypt_decrypt_control::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`external_device_encrypt_decrypt_control::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@external_device_encrypt_decrypt_control`] module"]
pub type EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL = crate::Reg<
    external_device_encrypt_decrypt_control::EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL_SPEC,
>;
#[doc = "EXTERNAL DEVICE ENCRYPTION/DECRYPTION configuration register"]
pub mod external_device_encrypt_decrypt_control;
#[doc = "SRAM_USAGE_CONF (rw) register accessor: HP memory usage configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sram_usage_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sram_usage_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sram_usage_conf`] module"]
pub type SRAM_USAGE_CONF = crate::Reg<sram_usage_conf::SRAM_USAGE_CONF_SPEC>;
#[doc = "HP memory usage configuration register"]
pub mod sram_usage_conf;
#[doc = "SEC_DPA_CONF (rw) register accessor: HP anti-DPA security configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sec_dpa_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sec_dpa_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sec_dpa_conf`] module"]
pub type SEC_DPA_CONF = crate::Reg<sec_dpa_conf::SEC_DPA_CONF_SPEC>;
#[doc = "HP anti-DPA security configuration register"]
pub mod sec_dpa_conf;
#[doc = "CPU_PERI_TIMEOUT_CONF (rw) register accessor: CPU_PERI_TIMEOUT configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_peri_timeout_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_peri_timeout_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_peri_timeout_conf`] module"]
pub type CPU_PERI_TIMEOUT_CONF = crate::Reg<cpu_peri_timeout_conf::CPU_PERI_TIMEOUT_CONF_SPEC>;
#[doc = "CPU_PERI_TIMEOUT configuration register"]
pub mod cpu_peri_timeout_conf;
#[doc = "CPU_PERI_TIMEOUT_ADDR (r) register accessor: CPU_PERI_TIMEOUT_ADDR register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_peri_timeout_addr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_peri_timeout_addr`] module"]
pub type CPU_PERI_TIMEOUT_ADDR = crate::Reg<cpu_peri_timeout_addr::CPU_PERI_TIMEOUT_ADDR_SPEC>;
#[doc = "CPU_PERI_TIMEOUT_ADDR register"]
pub mod cpu_peri_timeout_addr;
#[doc = "CPU_PERI_TIMEOUT_UID (r) register accessor: CPU_PERI_TIMEOUT_UID register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_peri_timeout_uid::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_peri_timeout_uid`] module"]
pub type CPU_PERI_TIMEOUT_UID = crate::Reg<cpu_peri_timeout_uid::CPU_PERI_TIMEOUT_UID_SPEC>;
#[doc = "CPU_PERI_TIMEOUT_UID register"]
pub mod cpu_peri_timeout_uid;
#[doc = "HP_PERI_TIMEOUT_CONF (rw) register accessor: HP_PERI_TIMEOUT configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_peri_timeout_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hp_peri_timeout_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hp_peri_timeout_conf`] module"]
pub type HP_PERI_TIMEOUT_CONF = crate::Reg<hp_peri_timeout_conf::HP_PERI_TIMEOUT_CONF_SPEC>;
#[doc = "HP_PERI_TIMEOUT configuration register"]
pub mod hp_peri_timeout_conf;
#[doc = "HP_PERI_TIMEOUT_ADDR (r) register accessor: HP_PERI_TIMEOUT_ADDR register\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_peri_timeout_addr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hp_peri_timeout_addr`] module"]
pub type HP_PERI_TIMEOUT_ADDR = crate::Reg<hp_peri_timeout_addr::HP_PERI_TIMEOUT_ADDR_SPEC>;
#[doc = "HP_PERI_TIMEOUT_ADDR register"]
pub mod hp_peri_timeout_addr;
#[doc = "HP_PERI_TIMEOUT_UID (r) register accessor: HP_PERI_TIMEOUT_UID register\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_peri_timeout_uid::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hp_peri_timeout_uid`] module"]
pub type HP_PERI_TIMEOUT_UID = crate::Reg<hp_peri_timeout_uid::HP_PERI_TIMEOUT_UID_SPEC>;
#[doc = "HP_PERI_TIMEOUT_UID register"]
pub mod hp_peri_timeout_uid;
#[doc = "MODEM_PERI_TIMEOUT_CONF (rw) register accessor: MODEM_PERI_TIMEOUT configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`modem_peri_timeout_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`modem_peri_timeout_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@modem_peri_timeout_conf`] module"]
pub type MODEM_PERI_TIMEOUT_CONF =
    crate::Reg<modem_peri_timeout_conf::MODEM_PERI_TIMEOUT_CONF_SPEC>;
#[doc = "MODEM_PERI_TIMEOUT configuration register"]
pub mod modem_peri_timeout_conf;
#[doc = "MODEM_PERI_TIMEOUT_ADDR (r) register accessor: MODEM_PERI_TIMEOUT_ADDR register\n\nYou can [`read`](crate::Reg::read) this register and get [`modem_peri_timeout_addr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@modem_peri_timeout_addr`] module"]
pub type MODEM_PERI_TIMEOUT_ADDR =
    crate::Reg<modem_peri_timeout_addr::MODEM_PERI_TIMEOUT_ADDR_SPEC>;
#[doc = "MODEM_PERI_TIMEOUT_ADDR register"]
pub mod modem_peri_timeout_addr;
#[doc = "MODEM_PERI_TIMEOUT_UID (r) register accessor: MODEM_PERI_TIMEOUT_UID register\n\nYou can [`read`](crate::Reg::read) this register and get [`modem_peri_timeout_uid::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@modem_peri_timeout_uid`] module"]
pub type MODEM_PERI_TIMEOUT_UID = crate::Reg<modem_peri_timeout_uid::MODEM_PERI_TIMEOUT_UID_SPEC>;
#[doc = "MODEM_PERI_TIMEOUT_UID register"]
pub mod modem_peri_timeout_uid;
#[doc = "SDIO_CTRL (rw) register accessor: SDIO Control configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sdio_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sdio_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sdio_ctrl`] module"]
pub type SDIO_CTRL = crate::Reg<sdio_ctrl::SDIO_CTRL_SPEC>;
#[doc = "SDIO Control configuration register"]
pub mod sdio_ctrl;
#[doc = "RETENTION_CONF (rw) register accessor: Retention configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`retention_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`retention_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@retention_conf`] module"]
pub type RETENTION_CONF = crate::Reg<retention_conf::RETENTION_CONF_SPEC>;
#[doc = "Retention configuration register"]
pub mod retention_conf;
#[doc = "ROM_TABLE_LOCK (rw) register accessor: Rom-Table lock register\n\nYou can [`read`](crate::Reg::read) this register and get [`rom_table_lock::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rom_table_lock::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rom_table_lock`] module"]
pub type ROM_TABLE_LOCK = crate::Reg<rom_table_lock::ROM_TABLE_LOCK_SPEC>;
#[doc = "Rom-Table lock register"]
pub mod rom_table_lock;
#[doc = "ROM_TABLE (rw) register accessor: Rom-Table register\n\nYou can [`read`](crate::Reg::read) this register and get [`rom_table::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rom_table::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rom_table`] module"]
pub type ROM_TABLE = crate::Reg<rom_table::ROM_TABLE_SPEC>;
#[doc = "Rom-Table register"]
pub mod rom_table;
#[doc = "CORE_DEBUG_RUNSTALL_CONF (rw) register accessor: Core Debug runstall configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`core_debug_runstall_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_debug_runstall_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_debug_runstall_conf`] module"]
pub type CORE_DEBUG_RUNSTALL_CONF =
    crate::Reg<core_debug_runstall_conf::CORE_DEBUG_RUNSTALL_CONF_SPEC>;
#[doc = "Core Debug runstall configure register"]
pub mod core_debug_runstall_conf;
#[doc = "MEM_TEST_CONF (rw) register accessor: MEM_TEST configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_test_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_test_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mem_test_conf`] module"]
pub type MEM_TEST_CONF = crate::Reg<mem_test_conf::MEM_TEST_CONF_SPEC>;
#[doc = "MEM_TEST configuration register"]
pub mod mem_test_conf;
#[doc = "RND_ECO (rw) register accessor: redcy eco register.\n\nYou can [`read`](crate::Reg::read) this register and get [`rnd_eco::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rnd_eco::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rnd_eco`] module"]
pub type RND_ECO = crate::Reg<rnd_eco::RND_ECO_SPEC>;
#[doc = "redcy eco register."]
pub mod rnd_eco;
#[doc = "RND_ECO_LOW (rw) register accessor: redcy eco low register.\n\nYou can [`read`](crate::Reg::read) this register and get [`rnd_eco_low::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rnd_eco_low::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rnd_eco_low`] module"]
pub type RND_ECO_LOW = crate::Reg<rnd_eco_low::RND_ECO_LOW_SPEC>;
#[doc = "redcy eco low register."]
pub mod rnd_eco_low;
#[doc = "RND_ECO_HIGH (rw) register accessor: redcy eco high register.\n\nYou can [`read`](crate::Reg::read) this register and get [`rnd_eco_high::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rnd_eco_high::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rnd_eco_high`] module"]
pub type RND_ECO_HIGH = crate::Reg<rnd_eco_high::RND_ECO_HIGH_SPEC>;
#[doc = "redcy eco high register."]
pub mod rnd_eco_high;
#[doc = "CLOCK_GATE (rw) register accessor: HP-SYSTEM clock gating configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`clock_gate::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clock_gate::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clock_gate`] module"]
pub type CLOCK_GATE = crate::Reg<clock_gate::CLOCK_GATE_SPEC>;
#[doc = "HP-SYSTEM clock gating configure register"]
pub mod clock_gate;
pub use crate::aes::{date, DATE};
