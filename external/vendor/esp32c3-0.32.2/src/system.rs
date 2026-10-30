#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    cpu_peri_clk_en: CPU_PERI_CLK_EN,
    cpu_peri_rst_en: CPU_PERI_RST_EN,
    cpu_per_conf: CPU_PER_CONF,
    mem_pd_mask: MEM_PD_MASK,
    perip_clk_en0: PERIP_CLK_EN0,
    perip_clk_en1: PERIP_CLK_EN1,
    perip_rst_en0: PERIP_RST_EN0,
    perip_rst_en1: PERIP_RST_EN1,
    bt_lpck_div_int: BT_LPCK_DIV_INT,
    bt_lpck_div_frac: BT_LPCK_DIV_FRAC,
    cpu_intr_from_cpu: [CPU_INTR_FROM_CPU; 4],
    rsa_pd_ctrl: RSA_PD_CTRL,
    edma_ctrl: EDMA_CTRL,
    cache_control: CACHE_CONTROL,
    external_device_encrypt_decrypt_control: EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL,
    rtc_fastmem_config: RTC_FASTMEM_CONFIG,
    rtc_fastmem_crc: RTC_FASTMEM_CRC,
    redundant_eco_ctrl: REDUNDANT_ECO_CTRL,
    clock_gate: CLOCK_GATE,
    sysclk_conf: SYSCLK_CONF,
    mem_pvt: MEM_PVT,
    comb_pvt_lvt_conf: COMB_PVT_LVT_CONF,
    comb_pvt_nvt_conf: COMB_PVT_NVT_CONF,
    comb_pvt_hvt_conf: COMB_PVT_HVT_CONF,
    comb_pvt_err_lvt_site0: COMB_PVT_ERR_LVT_SITE0,
    comb_pvt_err_nvt_site0: COMB_PVT_ERR_NVT_SITE0,
    comb_pvt_err_hvt_site0: COMB_PVT_ERR_HVT_SITE0,
    comb_pvt_err_lvt_site1: COMB_PVT_ERR_LVT_SITE1,
    comb_pvt_err_nvt_site1: COMB_PVT_ERR_NVT_SITE1,
    comb_pvt_err_hvt_site1: COMB_PVT_ERR_HVT_SITE1,
    comb_pvt_err_lvt_site2: COMB_PVT_ERR_LVT_SITE2,
    comb_pvt_err_nvt_site2: COMB_PVT_ERR_NVT_SITE2,
    comb_pvt_err_hvt_site2: COMB_PVT_ERR_HVT_SITE2,
    comb_pvt_err_lvt_site3: COMB_PVT_ERR_LVT_SITE3,
    comb_pvt_err_nvt_site3: COMB_PVT_ERR_NVT_SITE3,
    comb_pvt_err_hvt_site3: COMB_PVT_ERR_HVT_SITE3,
    _reserved36: [u8; 0x0f60],
    system_reg_date: SYSTEM_REG_DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - cpu_peripheral clock gating register"]
    #[inline(always)]
    pub const fn cpu_peri_clk_en(&self) -> &CPU_PERI_CLK_EN {
        &self.cpu_peri_clk_en
    }
    #[doc = "0x04 - cpu_peripheral reset register"]
    #[inline(always)]
    pub const fn cpu_peri_rst_en(&self) -> &CPU_PERI_RST_EN {
        &self.cpu_peri_rst_en
    }
    #[doc = "0x08 - cpu clock config register"]
    #[inline(always)]
    pub const fn cpu_per_conf(&self) -> &CPU_PER_CONF {
        &self.cpu_per_conf
    }
    #[doc = "0x0c - memory power down mask register"]
    #[inline(always)]
    pub const fn mem_pd_mask(&self) -> &MEM_PD_MASK {
        &self.mem_pd_mask
    }
    #[doc = "0x10 - peripheral clock gating register"]
    #[inline(always)]
    pub const fn perip_clk_en0(&self) -> &PERIP_CLK_EN0 {
        &self.perip_clk_en0
    }
    #[doc = "0x14 - peripheral clock gating register"]
    #[inline(always)]
    pub const fn perip_clk_en1(&self) -> &PERIP_CLK_EN1 {
        &self.perip_clk_en1
    }
    #[doc = "0x18 - reserved"]
    #[inline(always)]
    pub const fn perip_rst_en0(&self) -> &PERIP_RST_EN0 {
        &self.perip_rst_en0
    }
    #[doc = "0x1c - peripheral reset register"]
    #[inline(always)]
    pub const fn perip_rst_en1(&self) -> &PERIP_RST_EN1 {
        &self.perip_rst_en1
    }
    #[doc = "0x20 - clock config register"]
    #[inline(always)]
    pub const fn bt_lpck_div_int(&self) -> &BT_LPCK_DIV_INT {
        &self.bt_lpck_div_int
    }
    #[doc = "0x24 - clock config register"]
    #[inline(always)]
    pub const fn bt_lpck_div_frac(&self) -> &BT_LPCK_DIV_FRAC {
        &self.bt_lpck_div_frac
    }
    #[doc = "0x28..0x38 - interrupt generate register"]
    #[inline(always)]
    pub const fn cpu_intr_from_cpu(&self, n: usize) -> &CPU_INTR_FROM_CPU {
        &self.cpu_intr_from_cpu[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x28..0x38 - interrupt generate register"]
    #[inline(always)]
    pub fn cpu_intr_from_cpu_iter(&self) -> impl Iterator<Item = &CPU_INTR_FROM_CPU> {
        self.cpu_intr_from_cpu.iter()
    }
    #[doc = "0x38 - rsa memory power control register"]
    #[inline(always)]
    pub const fn rsa_pd_ctrl(&self) -> &RSA_PD_CTRL {
        &self.rsa_pd_ctrl
    }
    #[doc = "0x3c - EDMA clock and reset register"]
    #[inline(always)]
    pub const fn edma_ctrl(&self) -> &EDMA_CTRL {
        &self.edma_ctrl
    }
    #[doc = "0x40 - cache control register"]
    #[inline(always)]
    pub const fn cache_control(&self) -> &CACHE_CONTROL {
        &self.cache_control
    }
    #[doc = "0x44 - SYSTEM_EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL_REG"]
    #[inline(always)]
    pub const fn external_device_encrypt_decrypt_control(
        &self,
    ) -> &EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL {
        &self.external_device_encrypt_decrypt_control
    }
    #[doc = "0x48 - fast memory config register"]
    #[inline(always)]
    pub const fn rtc_fastmem_config(&self) -> &RTC_FASTMEM_CONFIG {
        &self.rtc_fastmem_config
    }
    #[doc = "0x4c - reserved"]
    #[inline(always)]
    pub const fn rtc_fastmem_crc(&self) -> &RTC_FASTMEM_CRC {
        &self.rtc_fastmem_crc
    }
    #[doc = "0x50 - eco register"]
    #[inline(always)]
    pub const fn redundant_eco_ctrl(&self) -> &REDUNDANT_ECO_CTRL {
        &self.redundant_eco_ctrl
    }
    #[doc = "0x54 - clock gating register"]
    #[inline(always)]
    pub const fn clock_gate(&self) -> &CLOCK_GATE {
        &self.clock_gate
    }
    #[doc = "0x58 - system clock config register"]
    #[inline(always)]
    pub const fn sysclk_conf(&self) -> &SYSCLK_CONF {
        &self.sysclk_conf
    }
    #[doc = "0x5c - mem pvt register"]
    #[inline(always)]
    pub const fn mem_pvt(&self) -> &MEM_PVT {
        &self.mem_pvt
    }
    #[doc = "0x60 - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_lvt_conf(&self) -> &COMB_PVT_LVT_CONF {
        &self.comb_pvt_lvt_conf
    }
    #[doc = "0x64 - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_nvt_conf(&self) -> &COMB_PVT_NVT_CONF {
        &self.comb_pvt_nvt_conf
    }
    #[doc = "0x68 - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_hvt_conf(&self) -> &COMB_PVT_HVT_CONF {
        &self.comb_pvt_hvt_conf
    }
    #[doc = "0x6c - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_err_lvt_site0(&self) -> &COMB_PVT_ERR_LVT_SITE0 {
        &self.comb_pvt_err_lvt_site0
    }
    #[doc = "0x70 - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_err_nvt_site0(&self) -> &COMB_PVT_ERR_NVT_SITE0 {
        &self.comb_pvt_err_nvt_site0
    }
    #[doc = "0x74 - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_err_hvt_site0(&self) -> &COMB_PVT_ERR_HVT_SITE0 {
        &self.comb_pvt_err_hvt_site0
    }
    #[doc = "0x78 - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_err_lvt_site1(&self) -> &COMB_PVT_ERR_LVT_SITE1 {
        &self.comb_pvt_err_lvt_site1
    }
    #[doc = "0x7c - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_err_nvt_site1(&self) -> &COMB_PVT_ERR_NVT_SITE1 {
        &self.comb_pvt_err_nvt_site1
    }
    #[doc = "0x80 - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_err_hvt_site1(&self) -> &COMB_PVT_ERR_HVT_SITE1 {
        &self.comb_pvt_err_hvt_site1
    }
    #[doc = "0x84 - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_err_lvt_site2(&self) -> &COMB_PVT_ERR_LVT_SITE2 {
        &self.comb_pvt_err_lvt_site2
    }
    #[doc = "0x88 - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_err_nvt_site2(&self) -> &COMB_PVT_ERR_NVT_SITE2 {
        &self.comb_pvt_err_nvt_site2
    }
    #[doc = "0x8c - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_err_hvt_site2(&self) -> &COMB_PVT_ERR_HVT_SITE2 {
        &self.comb_pvt_err_hvt_site2
    }
    #[doc = "0x90 - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_err_lvt_site3(&self) -> &COMB_PVT_ERR_LVT_SITE3 {
        &self.comb_pvt_err_lvt_site3
    }
    #[doc = "0x94 - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_err_nvt_site3(&self) -> &COMB_PVT_ERR_NVT_SITE3 {
        &self.comb_pvt_err_nvt_site3
    }
    #[doc = "0x98 - mem pvt register"]
    #[inline(always)]
    pub const fn comb_pvt_err_hvt_site3(&self) -> &COMB_PVT_ERR_HVT_SITE3 {
        &self.comb_pvt_err_hvt_site3
    }
    #[doc = "0xffc - Version register"]
    #[inline(always)]
    pub const fn system_reg_date(&self) -> &SYSTEM_REG_DATE {
        &self.system_reg_date
    }
}
#[doc = "CPU_PERI_CLK_EN (rw) register accessor: cpu_peripheral clock gating register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_peri_clk_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_peri_clk_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_peri_clk_en`] module"]
pub type CPU_PERI_CLK_EN = crate::Reg<cpu_peri_clk_en::CPU_PERI_CLK_EN_SPEC>;
#[doc = "cpu_peripheral clock gating register"]
pub mod cpu_peri_clk_en;
#[doc = "CPU_PERI_RST_EN (rw) register accessor: cpu_peripheral reset register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_peri_rst_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_peri_rst_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_peri_rst_en`] module"]
pub type CPU_PERI_RST_EN = crate::Reg<cpu_peri_rst_en::CPU_PERI_RST_EN_SPEC>;
#[doc = "cpu_peripheral reset register"]
pub mod cpu_peri_rst_en;
#[doc = "CPU_PER_CONF (rw) register accessor: cpu clock config register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_per_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_per_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_per_conf`] module"]
pub type CPU_PER_CONF = crate::Reg<cpu_per_conf::CPU_PER_CONF_SPEC>;
#[doc = "cpu clock config register"]
pub mod cpu_per_conf;
#[doc = "MEM_PD_MASK (rw) register accessor: memory power down mask register\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_pd_mask::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_pd_mask::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mem_pd_mask`] module"]
pub type MEM_PD_MASK = crate::Reg<mem_pd_mask::MEM_PD_MASK_SPEC>;
#[doc = "memory power down mask register"]
pub mod mem_pd_mask;
#[doc = "PERIP_CLK_EN0 (rw) register accessor: peripheral clock gating register\n\nYou can [`read`](crate::Reg::read) this register and get [`perip_clk_en0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`perip_clk_en0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@perip_clk_en0`] module"]
pub type PERIP_CLK_EN0 = crate::Reg<perip_clk_en0::PERIP_CLK_EN0_SPEC>;
#[doc = "peripheral clock gating register"]
pub mod perip_clk_en0;
#[doc = "PERIP_CLK_EN1 (rw) register accessor: peripheral clock gating register\n\nYou can [`read`](crate::Reg::read) this register and get [`perip_clk_en1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`perip_clk_en1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@perip_clk_en1`] module"]
pub type PERIP_CLK_EN1 = crate::Reg<perip_clk_en1::PERIP_CLK_EN1_SPEC>;
#[doc = "peripheral clock gating register"]
pub mod perip_clk_en1;
#[doc = "PERIP_RST_EN0 (rw) register accessor: reserved\n\nYou can [`read`](crate::Reg::read) this register and get [`perip_rst_en0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`perip_rst_en0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@perip_rst_en0`] module"]
pub type PERIP_RST_EN0 = crate::Reg<perip_rst_en0::PERIP_RST_EN0_SPEC>;
#[doc = "reserved"]
pub mod perip_rst_en0;
#[doc = "PERIP_RST_EN1 (rw) register accessor: peripheral reset register\n\nYou can [`read`](crate::Reg::read) this register and get [`perip_rst_en1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`perip_rst_en1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@perip_rst_en1`] module"]
pub type PERIP_RST_EN1 = crate::Reg<perip_rst_en1::PERIP_RST_EN1_SPEC>;
#[doc = "peripheral reset register"]
pub mod perip_rst_en1;
#[doc = "BT_LPCK_DIV_INT (rw) register accessor: clock config register\n\nYou can [`read`](crate::Reg::read) this register and get [`bt_lpck_div_int::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`bt_lpck_div_int::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bt_lpck_div_int`] module"]
pub type BT_LPCK_DIV_INT = crate::Reg<bt_lpck_div_int::BT_LPCK_DIV_INT_SPEC>;
#[doc = "clock config register"]
pub mod bt_lpck_div_int;
#[doc = "BT_LPCK_DIV_FRAC (rw) register accessor: clock config register\n\nYou can [`read`](crate::Reg::read) this register and get [`bt_lpck_div_frac::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`bt_lpck_div_frac::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bt_lpck_div_frac`] module"]
pub type BT_LPCK_DIV_FRAC = crate::Reg<bt_lpck_div_frac::BT_LPCK_DIV_FRAC_SPEC>;
#[doc = "clock config register"]
pub mod bt_lpck_div_frac;
#[doc = "CPU_INTR_FROM_CPU (rw) register accessor: interrupt generate register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_intr_from_cpu::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_intr_from_cpu::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_intr_from_cpu`] module"]
pub type CPU_INTR_FROM_CPU = crate::Reg<cpu_intr_from_cpu::CPU_INTR_FROM_CPU_SPEC>;
#[doc = "interrupt generate register"]
pub mod cpu_intr_from_cpu;
#[doc = "RSA_PD_CTRL (rw) register accessor: rsa memory power control register\n\nYou can [`read`](crate::Reg::read) this register and get [`rsa_pd_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rsa_pd_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rsa_pd_ctrl`] module"]
pub type RSA_PD_CTRL = crate::Reg<rsa_pd_ctrl::RSA_PD_CTRL_SPEC>;
#[doc = "rsa memory power control register"]
pub mod rsa_pd_ctrl;
#[doc = "EDMA_CTRL (rw) register accessor: EDMA clock and reset register\n\nYou can [`read`](crate::Reg::read) this register and get [`edma_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`edma_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@edma_ctrl`] module"]
pub type EDMA_CTRL = crate::Reg<edma_ctrl::EDMA_CTRL_SPEC>;
#[doc = "EDMA clock and reset register"]
pub mod edma_ctrl;
#[doc = "CACHE_CONTROL (rw) register accessor: cache control register\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_control::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_control::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_control`] module"]
pub type CACHE_CONTROL = crate::Reg<cache_control::CACHE_CONTROL_SPEC>;
#[doc = "cache control register"]
pub mod cache_control;
#[doc = "EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL (rw) register accessor: SYSTEM_EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`external_device_encrypt_decrypt_control::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`external_device_encrypt_decrypt_control::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@external_device_encrypt_decrypt_control`] module"]
pub type EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL = crate::Reg<
    external_device_encrypt_decrypt_control::EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL_SPEC,
>;
#[doc = "SYSTEM_EXTERNAL_DEVICE_ENCRYPT_DECRYPT_CONTROL_REG"]
pub mod external_device_encrypt_decrypt_control;
#[doc = "RTC_FASTMEM_CONFIG (rw) register accessor: fast memory config register\n\nYou can [`read`](crate::Reg::read) this register and get [`rtc_fastmem_config::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rtc_fastmem_config::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rtc_fastmem_config`] module"]
pub type RTC_FASTMEM_CONFIG = crate::Reg<rtc_fastmem_config::RTC_FASTMEM_CONFIG_SPEC>;
#[doc = "fast memory config register"]
pub mod rtc_fastmem_config;
#[doc = "RTC_FASTMEM_CRC (r) register accessor: reserved\n\nYou can [`read`](crate::Reg::read) this register and get [`rtc_fastmem_crc::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rtc_fastmem_crc`] module"]
pub type RTC_FASTMEM_CRC = crate::Reg<rtc_fastmem_crc::RTC_FASTMEM_CRC_SPEC>;
#[doc = "reserved"]
pub mod rtc_fastmem_crc;
#[doc = "REDUNDANT_ECO_CTRL (rw) register accessor: eco register\n\nYou can [`read`](crate::Reg::read) this register and get [`redundant_eco_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`redundant_eco_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@redundant_eco_ctrl`] module"]
pub type REDUNDANT_ECO_CTRL = crate::Reg<redundant_eco_ctrl::REDUNDANT_ECO_CTRL_SPEC>;
#[doc = "eco register"]
pub mod redundant_eco_ctrl;
#[doc = "CLOCK_GATE (rw) register accessor: clock gating register\n\nYou can [`read`](crate::Reg::read) this register and get [`clock_gate::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clock_gate::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clock_gate`] module"]
pub type CLOCK_GATE = crate::Reg<clock_gate::CLOCK_GATE_SPEC>;
#[doc = "clock gating register"]
pub mod clock_gate;
#[doc = "SYSCLK_CONF (rw) register accessor: system clock config register\n\nYou can [`read`](crate::Reg::read) this register and get [`sysclk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sysclk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sysclk_conf`] module"]
pub type SYSCLK_CONF = crate::Reg<sysclk_conf::SYSCLK_CONF_SPEC>;
#[doc = "system clock config register"]
pub mod sysclk_conf;
#[doc = "MEM_PVT (rw) register accessor: mem pvt register\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_pvt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_pvt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mem_pvt`] module"]
pub type MEM_PVT = crate::Reg<mem_pvt::MEM_PVT_SPEC>;
#[doc = "mem pvt register"]
pub mod mem_pvt;
#[doc = "COMB_PVT_LVT_CONF (rw) register accessor: mem pvt register\n\nYou can [`read`](crate::Reg::read) this register and get [`comb_pvt_lvt_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`comb_pvt_lvt_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@comb_pvt_lvt_conf`] module"]
pub type COMB_PVT_LVT_CONF = crate::Reg<comb_pvt_lvt_conf::COMB_PVT_LVT_CONF_SPEC>;
#[doc = "mem pvt register"]
pub mod comb_pvt_lvt_conf;
pub use comb_pvt_lvt_conf as comb_pvt_nvt_conf;
pub use comb_pvt_lvt_conf as comb_pvt_hvt_conf;
pub use COMB_PVT_LVT_CONF as COMB_PVT_NVT_CONF;
pub use COMB_PVT_LVT_CONF as COMB_PVT_HVT_CONF;
#[doc = "COMB_PVT_ERR_LVT_SITE0 (r) register accessor: mem pvt register\n\nYou can [`read`](crate::Reg::read) this register and get [`comb_pvt_err_lvt_site0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@comb_pvt_err_lvt_site0`] module"]
pub type COMB_PVT_ERR_LVT_SITE0 = crate::Reg<comb_pvt_err_lvt_site0::COMB_PVT_ERR_LVT_SITE0_SPEC>;
#[doc = "mem pvt register"]
pub mod comb_pvt_err_lvt_site0;
pub use comb_pvt_err_lvt_site0 as comb_pvt_err_nvt_site0;
pub use comb_pvt_err_lvt_site0 as comb_pvt_err_hvt_site0;
pub use comb_pvt_err_lvt_site0 as comb_pvt_err_lvt_site1;
pub use comb_pvt_err_lvt_site0 as comb_pvt_err_nvt_site1;
pub use comb_pvt_err_lvt_site0 as comb_pvt_err_hvt_site1;
pub use comb_pvt_err_lvt_site0 as comb_pvt_err_lvt_site2;
pub use comb_pvt_err_lvt_site0 as comb_pvt_err_nvt_site2;
pub use comb_pvt_err_lvt_site0 as comb_pvt_err_hvt_site2;
pub use comb_pvt_err_lvt_site0 as comb_pvt_err_lvt_site3;
pub use comb_pvt_err_lvt_site0 as comb_pvt_err_nvt_site3;
pub use comb_pvt_err_lvt_site0 as comb_pvt_err_hvt_site3;
pub use COMB_PVT_ERR_LVT_SITE0 as COMB_PVT_ERR_NVT_SITE0;
pub use COMB_PVT_ERR_LVT_SITE0 as COMB_PVT_ERR_HVT_SITE0;
pub use COMB_PVT_ERR_LVT_SITE0 as COMB_PVT_ERR_LVT_SITE1;
pub use COMB_PVT_ERR_LVT_SITE0 as COMB_PVT_ERR_NVT_SITE1;
pub use COMB_PVT_ERR_LVT_SITE0 as COMB_PVT_ERR_HVT_SITE1;
pub use COMB_PVT_ERR_LVT_SITE0 as COMB_PVT_ERR_LVT_SITE2;
pub use COMB_PVT_ERR_LVT_SITE0 as COMB_PVT_ERR_NVT_SITE2;
pub use COMB_PVT_ERR_LVT_SITE0 as COMB_PVT_ERR_HVT_SITE2;
pub use COMB_PVT_ERR_LVT_SITE0 as COMB_PVT_ERR_LVT_SITE3;
pub use COMB_PVT_ERR_LVT_SITE0 as COMB_PVT_ERR_NVT_SITE3;
pub use COMB_PVT_ERR_LVT_SITE0 as COMB_PVT_ERR_HVT_SITE3;

pub use crate::aes::{date as system_reg_date, DATE as SYSTEM_REG_DATE};
