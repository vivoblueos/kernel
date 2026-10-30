#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    sysclk_conf: SYSCLK_CONF,
    tick_conf: TICK_CONF,
    clk_out_en: CLK_OUT_EN,
    wifi_bb_cfg: WIFI_BB_CFG,
    wifi_bb_cfg_2: WIFI_BB_CFG_2,
    wifi_clk_en: WIFI_CLK_EN,
    wifi_rst_en: WIFI_RST_EN,
    host_inf_sel: HOST_INF_SEL,
    ext_mem_pms_lock: EXT_MEM_PMS_LOCK,
    _reserved9: [u8; 0x04],
    flash_ace0_attr: FLASH_ACE0_ATTR,
    flash_ace1_attr: FLASH_ACE1_ATTR,
    flash_ace2_attr: FLASH_ACE2_ATTR,
    flash_ace3_attr: FLASH_ACE3_ATTR,
    flash_ace0_addr: FLASH_ACE0_ADDR,
    flash_ace1_addr: FLASH_ACE1_ADDR,
    flash_ace2_addr: FLASH_ACE2_ADDR,
    flash_ace3_addr: FLASH_ACE3_ADDR,
    flash_ace0_size: FLASH_ACE0_SIZE,
    flash_ace1_size: FLASH_ACE1_SIZE,
    flash_ace2_size: FLASH_ACE2_SIZE,
    flash_ace3_size: FLASH_ACE3_SIZE,
    _reserved21: [u8; 0x30],
    spi_mem_pms_ctrl: SPI_MEM_PMS_CTRL,
    spi_mem_reject_addr: SPI_MEM_REJECT_ADDR,
    sdio_ctrl: SDIO_CTRL,
    redcy_sig0: REDCY_SIG0,
    redcy_sig1: REDCY_SIG1,
    front_end_mem_pd: FRONT_END_MEM_PD,
    retention_ctrl: RETENTION_CTRL,
    clkgate_force_on: CLKGATE_FORCE_ON,
    mem_power_down: MEM_POWER_DOWN,
    mem_power_up: MEM_POWER_UP,
    rnd_data: RND_DATA,
    peri_backup_config: PERI_BACKUP_CONFIG,
    peri_backup_apb_addr: PERI_BACKUP_APB_ADDR,
    peri_backup_mem_addr: PERI_BACKUP_MEM_ADDR,
    peri_backup_int_raw: PERI_BACKUP_INT_RAW,
    peri_backup_int_st: PERI_BACKUP_INT_ST,
    peri_backup_int_ena: PERI_BACKUP_INT_ENA,
    _reserved38: [u8; 0x04],
    peri_backup_int_clr: PERI_BACKUP_INT_CLR,
    _reserved39: [u8; 0x0328],
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - APB_CTRL_SYSCLK_CONF_REG"]
    #[inline(always)]
    pub const fn sysclk_conf(&self) -> &SYSCLK_CONF {
        &self.sysclk_conf
    }
    #[doc = "0x04 - APB_CTRL_TICK_CONF_REG"]
    #[inline(always)]
    pub const fn tick_conf(&self) -> &TICK_CONF {
        &self.tick_conf
    }
    #[doc = "0x08 - APB_CTRL_CLK_OUT_EN_REG"]
    #[inline(always)]
    pub const fn clk_out_en(&self) -> &CLK_OUT_EN {
        &self.clk_out_en
    }
    #[doc = "0x0c - APB_CTRL_WIFI_BB_CFG_REG"]
    #[inline(always)]
    pub const fn wifi_bb_cfg(&self) -> &WIFI_BB_CFG {
        &self.wifi_bb_cfg
    }
    #[doc = "0x10 - APB_CTRL_WIFI_BB_CFG_2_REG"]
    #[inline(always)]
    pub const fn wifi_bb_cfg_2(&self) -> &WIFI_BB_CFG_2 {
        &self.wifi_bb_cfg_2
    }
    #[doc = "0x14 - APB_CTRL_WIFI_CLK_EN_REG"]
    #[inline(always)]
    pub const fn wifi_clk_en(&self) -> &WIFI_CLK_EN {
        &self.wifi_clk_en
    }
    #[doc = "0x18 - APB_CTRL_WIFI_RST_EN_REG"]
    #[inline(always)]
    pub const fn wifi_rst_en(&self) -> &WIFI_RST_EN {
        &self.wifi_rst_en
    }
    #[doc = "0x1c - APB_CTRL_HOST_INF_SEL_REG"]
    #[inline(always)]
    pub const fn host_inf_sel(&self) -> &HOST_INF_SEL {
        &self.host_inf_sel
    }
    #[doc = "0x20 - APB_CTRL_EXT_MEM_PMS_LOCK_REG"]
    #[inline(always)]
    pub const fn ext_mem_pms_lock(&self) -> &EXT_MEM_PMS_LOCK {
        &self.ext_mem_pms_lock
    }
    #[doc = "0x28 - APB_CTRL_FLASH_ACE0_ATTR_REG"]
    #[inline(always)]
    pub const fn flash_ace0_attr(&self) -> &FLASH_ACE0_ATTR {
        &self.flash_ace0_attr
    }
    #[doc = "0x2c - APB_CTRL_FLASH_ACE1_ATTR_REG"]
    #[inline(always)]
    pub const fn flash_ace1_attr(&self) -> &FLASH_ACE1_ATTR {
        &self.flash_ace1_attr
    }
    #[doc = "0x30 - APB_CTRL_FLASH_ACE2_ATTR_REG"]
    #[inline(always)]
    pub const fn flash_ace2_attr(&self) -> &FLASH_ACE2_ATTR {
        &self.flash_ace2_attr
    }
    #[doc = "0x34 - APB_CTRL_FLASH_ACE3_ATTR_REG"]
    #[inline(always)]
    pub const fn flash_ace3_attr(&self) -> &FLASH_ACE3_ATTR {
        &self.flash_ace3_attr
    }
    #[doc = "0x38 - APB_CTRL_FLASH_ACE0_ADDR_REG"]
    #[inline(always)]
    pub const fn flash_ace0_addr(&self) -> &FLASH_ACE0_ADDR {
        &self.flash_ace0_addr
    }
    #[doc = "0x3c - APB_CTRL_FLASH_ACE1_ADDR_REG"]
    #[inline(always)]
    pub const fn flash_ace1_addr(&self) -> &FLASH_ACE1_ADDR {
        &self.flash_ace1_addr
    }
    #[doc = "0x40 - APB_CTRL_FLASH_ACE2_ADDR_REG"]
    #[inline(always)]
    pub const fn flash_ace2_addr(&self) -> &FLASH_ACE2_ADDR {
        &self.flash_ace2_addr
    }
    #[doc = "0x44 - APB_CTRL_FLASH_ACE3_ADDR_REG"]
    #[inline(always)]
    pub const fn flash_ace3_addr(&self) -> &FLASH_ACE3_ADDR {
        &self.flash_ace3_addr
    }
    #[doc = "0x48 - APB_CTRL_FLASH_ACE0_SIZE_REG"]
    #[inline(always)]
    pub const fn flash_ace0_size(&self) -> &FLASH_ACE0_SIZE {
        &self.flash_ace0_size
    }
    #[doc = "0x4c - APB_CTRL_FLASH_ACE1_SIZE_REG"]
    #[inline(always)]
    pub const fn flash_ace1_size(&self) -> &FLASH_ACE1_SIZE {
        &self.flash_ace1_size
    }
    #[doc = "0x50 - APB_CTRL_FLASH_ACE2_SIZE_REG"]
    #[inline(always)]
    pub const fn flash_ace2_size(&self) -> &FLASH_ACE2_SIZE {
        &self.flash_ace2_size
    }
    #[doc = "0x54 - APB_CTRL_FLASH_ACE3_SIZE_REG"]
    #[inline(always)]
    pub const fn flash_ace3_size(&self) -> &FLASH_ACE3_SIZE {
        &self.flash_ace3_size
    }
    #[doc = "0x88 - APB_CTRL_SPI_MEM_PMS_CTRL_REG"]
    #[inline(always)]
    pub const fn spi_mem_pms_ctrl(&self) -> &SPI_MEM_PMS_CTRL {
        &self.spi_mem_pms_ctrl
    }
    #[doc = "0x8c - APB_CTRL_SPI_MEM_REJECT_ADDR_REG"]
    #[inline(always)]
    pub const fn spi_mem_reject_addr(&self) -> &SPI_MEM_REJECT_ADDR {
        &self.spi_mem_reject_addr
    }
    #[doc = "0x90 - APB_CTRL_SDIO_CTRL_REG"]
    #[inline(always)]
    pub const fn sdio_ctrl(&self) -> &SDIO_CTRL {
        &self.sdio_ctrl
    }
    #[doc = "0x94 - APB_CTRL_REDCY_SIG0_REG"]
    #[inline(always)]
    pub const fn redcy_sig0(&self) -> &REDCY_SIG0 {
        &self.redcy_sig0
    }
    #[doc = "0x98 - APB_CTRL_REDCY_SIG1_REG"]
    #[inline(always)]
    pub const fn redcy_sig1(&self) -> &REDCY_SIG1 {
        &self.redcy_sig1
    }
    #[doc = "0x9c - APB_CTRL_FRONT_END_MEM_PD_REG"]
    #[inline(always)]
    pub const fn front_end_mem_pd(&self) -> &FRONT_END_MEM_PD {
        &self.front_end_mem_pd
    }
    #[doc = "0xa0 - APB_CTRL_RETENTION_CTRL_REG"]
    #[inline(always)]
    pub const fn retention_ctrl(&self) -> &RETENTION_CTRL {
        &self.retention_ctrl
    }
    #[doc = "0xa4 - APB_CTRL_CLKGATE_FORCE_ON_REG"]
    #[inline(always)]
    pub const fn clkgate_force_on(&self) -> &CLKGATE_FORCE_ON {
        &self.clkgate_force_on
    }
    #[doc = "0xa8 - APB_CTRL_MEM_POWER_DOWN_REG"]
    #[inline(always)]
    pub const fn mem_power_down(&self) -> &MEM_POWER_DOWN {
        &self.mem_power_down
    }
    #[doc = "0xac - APB_CTRL_MEM_POWER_UP_REG"]
    #[inline(always)]
    pub const fn mem_power_up(&self) -> &MEM_POWER_UP {
        &self.mem_power_up
    }
    #[doc = "0xb0 - APB_CTRL_RND_DATA_REG"]
    #[inline(always)]
    pub const fn rnd_data(&self) -> &RND_DATA {
        &self.rnd_data
    }
    #[doc = "0xb4 - APB_CTRL_PERI_BACKUP_CONFIG_REG"]
    #[inline(always)]
    pub const fn peri_backup_config(&self) -> &PERI_BACKUP_CONFIG {
        &self.peri_backup_config
    }
    #[doc = "0xb8 - APB_CTRL_PERI_BACKUP_APB_ADDR_REG"]
    #[inline(always)]
    pub const fn peri_backup_apb_addr(&self) -> &PERI_BACKUP_APB_ADDR {
        &self.peri_backup_apb_addr
    }
    #[doc = "0xbc - APB_CTRL_PERI_BACKUP_MEM_ADDR_REG"]
    #[inline(always)]
    pub const fn peri_backup_mem_addr(&self) -> &PERI_BACKUP_MEM_ADDR {
        &self.peri_backup_mem_addr
    }
    #[doc = "0xc0 - APB_CTRL_PERI_BACKUP_INT_RAW_REG"]
    #[inline(always)]
    pub const fn peri_backup_int_raw(&self) -> &PERI_BACKUP_INT_RAW {
        &self.peri_backup_int_raw
    }
    #[doc = "0xc4 - APB_CTRL_PERI_BACKUP_INT_ST_REG"]
    #[inline(always)]
    pub const fn peri_backup_int_st(&self) -> &PERI_BACKUP_INT_ST {
        &self.peri_backup_int_st
    }
    #[doc = "0xc8 - APB_CTRL_PERI_BACKUP_INT_ENA_REG"]
    #[inline(always)]
    pub const fn peri_backup_int_ena(&self) -> &PERI_BACKUP_INT_ENA {
        &self.peri_backup_int_ena
    }
    #[doc = "0xd0 - APB_CTRL_PERI_BACKUP_INT_CLR_REG"]
    #[inline(always)]
    pub const fn peri_backup_int_clr(&self) -> &PERI_BACKUP_INT_CLR {
        &self.peri_backup_int_clr
    }
    #[doc = "0x3fc - APB_CTRL_DATE_REG"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "SYSCLK_CONF (rw) register accessor: APB_CTRL_SYSCLK_CONF_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`sysclk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sysclk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sysclk_conf`] module"]
pub type SYSCLK_CONF = crate::Reg<sysclk_conf::SYSCLK_CONF_SPEC>;
#[doc = "APB_CTRL_SYSCLK_CONF_REG"]
pub mod sysclk_conf;
#[doc = "TICK_CONF (rw) register accessor: APB_CTRL_TICK_CONF_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`tick_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tick_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tick_conf`] module"]
pub type TICK_CONF = crate::Reg<tick_conf::TICK_CONF_SPEC>;
#[doc = "APB_CTRL_TICK_CONF_REG"]
pub mod tick_conf;
#[doc = "CLK_OUT_EN (rw) register accessor: APB_CTRL_CLK_OUT_EN_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_out_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_out_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clk_out_en`] module"]
pub type CLK_OUT_EN = crate::Reg<clk_out_en::CLK_OUT_EN_SPEC>;
#[doc = "APB_CTRL_CLK_OUT_EN_REG"]
pub mod clk_out_en;
#[doc = "WIFI_BB_CFG (rw) register accessor: APB_CTRL_WIFI_BB_CFG_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`wifi_bb_cfg::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wifi_bb_cfg::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wifi_bb_cfg`] module"]
pub type WIFI_BB_CFG = crate::Reg<wifi_bb_cfg::WIFI_BB_CFG_SPEC>;
#[doc = "APB_CTRL_WIFI_BB_CFG_REG"]
pub mod wifi_bb_cfg;
#[doc = "WIFI_BB_CFG_2 (rw) register accessor: APB_CTRL_WIFI_BB_CFG_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`wifi_bb_cfg_2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wifi_bb_cfg_2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wifi_bb_cfg_2`] module"]
pub type WIFI_BB_CFG_2 = crate::Reg<wifi_bb_cfg_2::WIFI_BB_CFG_2_SPEC>;
#[doc = "APB_CTRL_WIFI_BB_CFG_2_REG"]
pub mod wifi_bb_cfg_2;
#[doc = "WIFI_CLK_EN (rw) register accessor: APB_CTRL_WIFI_CLK_EN_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`wifi_clk_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wifi_clk_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wifi_clk_en`] module"]
pub type WIFI_CLK_EN = crate::Reg<wifi_clk_en::WIFI_CLK_EN_SPEC>;
#[doc = "APB_CTRL_WIFI_CLK_EN_REG"]
pub mod wifi_clk_en;
#[doc = "WIFI_RST_EN (rw) register accessor: APB_CTRL_WIFI_RST_EN_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`wifi_rst_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wifi_rst_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wifi_rst_en`] module"]
pub type WIFI_RST_EN = crate::Reg<wifi_rst_en::WIFI_RST_EN_SPEC>;
#[doc = "APB_CTRL_WIFI_RST_EN_REG"]
pub mod wifi_rst_en;
#[doc = "HOST_INF_SEL (rw) register accessor: APB_CTRL_HOST_INF_SEL_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`host_inf_sel::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`host_inf_sel::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@host_inf_sel`] module"]
pub type HOST_INF_SEL = crate::Reg<host_inf_sel::HOST_INF_SEL_SPEC>;
#[doc = "APB_CTRL_HOST_INF_SEL_REG"]
pub mod host_inf_sel;
#[doc = "EXT_MEM_PMS_LOCK (rw) register accessor: APB_CTRL_EXT_MEM_PMS_LOCK_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`ext_mem_pms_lock::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ext_mem_pms_lock::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ext_mem_pms_lock`] module"]
pub type EXT_MEM_PMS_LOCK = crate::Reg<ext_mem_pms_lock::EXT_MEM_PMS_LOCK_SPEC>;
#[doc = "APB_CTRL_EXT_MEM_PMS_LOCK_REG"]
pub mod ext_mem_pms_lock;
#[doc = "FLASH_ACE0_ATTR (rw) register accessor: APB_CTRL_FLASH_ACE0_ATTR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`flash_ace0_attr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`flash_ace0_attr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@flash_ace0_attr`] module"]
pub type FLASH_ACE0_ATTR = crate::Reg<flash_ace0_attr::FLASH_ACE0_ATTR_SPEC>;
#[doc = "APB_CTRL_FLASH_ACE0_ATTR_REG"]
pub mod flash_ace0_attr;
pub use flash_ace0_attr as flash_ace1_attr;
pub use flash_ace0_attr as flash_ace2_attr;
pub use flash_ace0_attr as flash_ace3_attr;
pub use FLASH_ACE0_ATTR as FLASH_ACE1_ATTR;
pub use FLASH_ACE0_ATTR as FLASH_ACE2_ATTR;
pub use FLASH_ACE0_ATTR as FLASH_ACE3_ATTR;
#[doc = "FLASH_ACE0_ADDR (rw) register accessor: APB_CTRL_FLASH_ACE0_ADDR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`flash_ace0_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`flash_ace0_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@flash_ace0_addr`] module"]
pub type FLASH_ACE0_ADDR = crate::Reg<flash_ace0_addr::FLASH_ACE0_ADDR_SPEC>;
#[doc = "APB_CTRL_FLASH_ACE0_ADDR_REG"]
pub mod flash_ace0_addr;
pub use flash_ace0_addr as flash_ace1_addr;
pub use flash_ace0_addr as flash_ace2_addr;
pub use flash_ace0_addr as flash_ace3_addr;
pub use FLASH_ACE0_ADDR as FLASH_ACE1_ADDR;
pub use FLASH_ACE0_ADDR as FLASH_ACE2_ADDR;
pub use FLASH_ACE0_ADDR as FLASH_ACE3_ADDR;
#[doc = "FLASH_ACE0_SIZE (rw) register accessor: APB_CTRL_FLASH_ACE0_SIZE_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`flash_ace0_size::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`flash_ace0_size::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@flash_ace0_size`] module"]
pub type FLASH_ACE0_SIZE = crate::Reg<flash_ace0_size::FLASH_ACE0_SIZE_SPEC>;
#[doc = "APB_CTRL_FLASH_ACE0_SIZE_REG"]
pub mod flash_ace0_size;
pub use flash_ace0_size as flash_ace1_size;
pub use flash_ace0_size as flash_ace2_size;
pub use flash_ace0_size as flash_ace3_size;
pub use FLASH_ACE0_SIZE as FLASH_ACE1_SIZE;
pub use FLASH_ACE0_SIZE as FLASH_ACE2_SIZE;
pub use FLASH_ACE0_SIZE as FLASH_ACE3_SIZE;
#[doc = "SPI_MEM_PMS_CTRL (rw) register accessor: APB_CTRL_SPI_MEM_PMS_CTRL_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`spi_mem_pms_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`spi_mem_pms_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@spi_mem_pms_ctrl`] module"]
pub type SPI_MEM_PMS_CTRL = crate::Reg<spi_mem_pms_ctrl::SPI_MEM_PMS_CTRL_SPEC>;
#[doc = "APB_CTRL_SPI_MEM_PMS_CTRL_REG"]
pub mod spi_mem_pms_ctrl;
#[doc = "SPI_MEM_REJECT_ADDR (r) register accessor: APB_CTRL_SPI_MEM_REJECT_ADDR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`spi_mem_reject_addr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@spi_mem_reject_addr`] module"]
pub type SPI_MEM_REJECT_ADDR = crate::Reg<spi_mem_reject_addr::SPI_MEM_REJECT_ADDR_SPEC>;
#[doc = "APB_CTRL_SPI_MEM_REJECT_ADDR_REG"]
pub mod spi_mem_reject_addr;
#[doc = "SDIO_CTRL (rw) register accessor: APB_CTRL_SDIO_CTRL_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`sdio_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sdio_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sdio_ctrl`] module"]
pub type SDIO_CTRL = crate::Reg<sdio_ctrl::SDIO_CTRL_SPEC>;
#[doc = "APB_CTRL_SDIO_CTRL_REG"]
pub mod sdio_ctrl;
#[doc = "REDCY_SIG0 (rw) register accessor: APB_CTRL_REDCY_SIG0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`redcy_sig0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`redcy_sig0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@redcy_sig0`] module"]
pub type REDCY_SIG0 = crate::Reg<redcy_sig0::REDCY_SIG0_SPEC>;
#[doc = "APB_CTRL_REDCY_SIG0_REG"]
pub mod redcy_sig0;
#[doc = "REDCY_SIG1 (rw) register accessor: APB_CTRL_REDCY_SIG1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`redcy_sig1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`redcy_sig1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@redcy_sig1`] module"]
pub type REDCY_SIG1 = crate::Reg<redcy_sig1::REDCY_SIG1_SPEC>;
#[doc = "APB_CTRL_REDCY_SIG1_REG"]
pub mod redcy_sig1;
#[doc = "FRONT_END_MEM_PD (rw) register accessor: APB_CTRL_FRONT_END_MEM_PD_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`front_end_mem_pd::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`front_end_mem_pd::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@front_end_mem_pd`] module"]
pub type FRONT_END_MEM_PD = crate::Reg<front_end_mem_pd::FRONT_END_MEM_PD_SPEC>;
#[doc = "APB_CTRL_FRONT_END_MEM_PD_REG"]
pub mod front_end_mem_pd;
#[doc = "RETENTION_CTRL (rw) register accessor: APB_CTRL_RETENTION_CTRL_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`retention_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`retention_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@retention_ctrl`] module"]
pub type RETENTION_CTRL = crate::Reg<retention_ctrl::RETENTION_CTRL_SPEC>;
#[doc = "APB_CTRL_RETENTION_CTRL_REG"]
pub mod retention_ctrl;
#[doc = "CLKGATE_FORCE_ON (rw) register accessor: APB_CTRL_CLKGATE_FORCE_ON_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`clkgate_force_on::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clkgate_force_on::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clkgate_force_on`] module"]
pub type CLKGATE_FORCE_ON = crate::Reg<clkgate_force_on::CLKGATE_FORCE_ON_SPEC>;
#[doc = "APB_CTRL_CLKGATE_FORCE_ON_REG"]
pub mod clkgate_force_on;
#[doc = "MEM_POWER_DOWN (rw) register accessor: APB_CTRL_MEM_POWER_DOWN_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_power_down::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_power_down::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mem_power_down`] module"]
pub type MEM_POWER_DOWN = crate::Reg<mem_power_down::MEM_POWER_DOWN_SPEC>;
#[doc = "APB_CTRL_MEM_POWER_DOWN_REG"]
pub mod mem_power_down;
#[doc = "MEM_POWER_UP (rw) register accessor: APB_CTRL_MEM_POWER_UP_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_power_up::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_power_up::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mem_power_up`] module"]
pub type MEM_POWER_UP = crate::Reg<mem_power_up::MEM_POWER_UP_SPEC>;
#[doc = "APB_CTRL_MEM_POWER_UP_REG"]
pub mod mem_power_up;
#[doc = "RND_DATA (r) register accessor: APB_CTRL_RND_DATA_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`rnd_data::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rnd_data`] module"]
pub type RND_DATA = crate::Reg<rnd_data::RND_DATA_SPEC>;
#[doc = "APB_CTRL_RND_DATA_REG"]
pub mod rnd_data;
#[doc = "PERI_BACKUP_CONFIG (rw) register accessor: APB_CTRL_PERI_BACKUP_CONFIG_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`peri_backup_config::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`peri_backup_config::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@peri_backup_config`] module"]
pub type PERI_BACKUP_CONFIG = crate::Reg<peri_backup_config::PERI_BACKUP_CONFIG_SPEC>;
#[doc = "APB_CTRL_PERI_BACKUP_CONFIG_REG"]
pub mod peri_backup_config;
#[doc = "PERI_BACKUP_APB_ADDR (rw) register accessor: APB_CTRL_PERI_BACKUP_APB_ADDR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`peri_backup_apb_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`peri_backup_apb_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@peri_backup_apb_addr`] module"]
pub type PERI_BACKUP_APB_ADDR = crate::Reg<peri_backup_apb_addr::PERI_BACKUP_APB_ADDR_SPEC>;
#[doc = "APB_CTRL_PERI_BACKUP_APB_ADDR_REG"]
pub mod peri_backup_apb_addr;
#[doc = "PERI_BACKUP_MEM_ADDR (rw) register accessor: APB_CTRL_PERI_BACKUP_MEM_ADDR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`peri_backup_mem_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`peri_backup_mem_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@peri_backup_mem_addr`] module"]
pub type PERI_BACKUP_MEM_ADDR = crate::Reg<peri_backup_mem_addr::PERI_BACKUP_MEM_ADDR_SPEC>;
#[doc = "APB_CTRL_PERI_BACKUP_MEM_ADDR_REG"]
pub mod peri_backup_mem_addr;
#[doc = "PERI_BACKUP_INT_RAW (r) register accessor: APB_CTRL_PERI_BACKUP_INT_RAW_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`peri_backup_int_raw::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@peri_backup_int_raw`] module"]
pub type PERI_BACKUP_INT_RAW = crate::Reg<peri_backup_int_raw::PERI_BACKUP_INT_RAW_SPEC>;
#[doc = "APB_CTRL_PERI_BACKUP_INT_RAW_REG"]
pub mod peri_backup_int_raw;
#[doc = "PERI_BACKUP_INT_ST (r) register accessor: APB_CTRL_PERI_BACKUP_INT_ST_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`peri_backup_int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@peri_backup_int_st`] module"]
pub type PERI_BACKUP_INT_ST = crate::Reg<peri_backup_int_st::PERI_BACKUP_INT_ST_SPEC>;
#[doc = "APB_CTRL_PERI_BACKUP_INT_ST_REG"]
pub mod peri_backup_int_st;
#[doc = "PERI_BACKUP_INT_ENA (rw) register accessor: APB_CTRL_PERI_BACKUP_INT_ENA_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`peri_backup_int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`peri_backup_int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@peri_backup_int_ena`] module"]
pub type PERI_BACKUP_INT_ENA = crate::Reg<peri_backup_int_ena::PERI_BACKUP_INT_ENA_SPEC>;
#[doc = "APB_CTRL_PERI_BACKUP_INT_ENA_REG"]
pub mod peri_backup_int_ena;
#[doc = "PERI_BACKUP_INT_CLR (w) register accessor: APB_CTRL_PERI_BACKUP_INT_CLR_REG\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`peri_backup_int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@peri_backup_int_clr`] module"]
pub type PERI_BACKUP_INT_CLR = crate::Reg<peri_backup_int_clr::PERI_BACKUP_INT_CLR_SPEC>;
#[doc = "APB_CTRL_PERI_BACKUP_INT_CLR_REG"]
pub mod peri_backup_int_clr;
pub use crate::aes::{date, DATE};
