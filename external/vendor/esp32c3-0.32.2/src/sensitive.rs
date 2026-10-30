#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    rom_table_lock: ROM_TABLE_LOCK,
    rom_table: ROM_TABLE,
    privilege_mode_sel_lock: PRIVILEGE_MODE_SEL_LOCK,
    privilege_mode_sel: PRIVILEGE_MODE_SEL,
    apb_peripheral_access_0: APB_PERIPHERAL_ACCESS_0,
    apb_peripheral_access_1: APB_PERIPHERAL_ACCESS_1,
    internal_sram_usage_0: INTERNAL_SRAM_USAGE_0,
    internal_sram_usage_1: INTERNAL_SRAM_USAGE_1,
    internal_sram_usage_3: INTERNAL_SRAM_USAGE_3,
    internal_sram_usage_4: INTERNAL_SRAM_USAGE_4,
    cache_tag_access_0: CACHE_TAG_ACCESS_0,
    cache_tag_access_1: CACHE_TAG_ACCESS_1,
    cache_mmu_access_0: CACHE_MMU_ACCESS_0,
    cache_mmu_access_1: CACHE_MMU_ACCESS_1,
    dma_apbperi: [DMA_APBPERI; 9],
    dma_apbperi_pms_monitor_0: DMA_APBPERI_PMS_MONITOR_0,
    dma_apbperi_pms_monitor_1: DMA_APBPERI_PMS_MONITOR_1,
    dma_apbperi_pms_monitor_2: DMA_APBPERI_PMS_MONITOR_2,
    dma_apbperi_pms_monitor_3: DMA_APBPERI_PMS_MONITOR_3,
    core_x_iram0_dram0_dma_split_line_constrain_0: CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_0,
    core_x_iram0_dram0_dma_split_line_constrain_1: CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_1,
    core_x_iram0_dram0_dma_split_line_constrain_2: CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_2,
    core_x_iram0_dram0_dma_split_line_constrain_3: CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_3,
    core_x_iram0_dram0_dma_split_line_constrain_4: CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_4,
    core_x_iram0_dram0_dma_split_line_constrain_5: CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_5,
    core_x_iram0_pms_constrain_0: CORE_X_IRAM0_PMS_CONSTRAIN_0,
    core_x_iram0_pms_constrain_1: CORE_X_IRAM0_PMS_CONSTRAIN_1,
    core_x_iram0_pms_constrain_2: CORE_X_IRAM0_PMS_CONSTRAIN_2,
    core_0_iram0_pms_monitor_0: CORE_0_IRAM0_PMS_MONITOR_0,
    core_0_iram0_pms_monitor_1: CORE_0_IRAM0_PMS_MONITOR_1,
    core_0_iram0_pms_monitor_2: CORE_0_IRAM0_PMS_MONITOR_2,
    core_x_dram0_pms_constrain_0: CORE_X_DRAM0_PMS_CONSTRAIN_0,
    core_x_dram0_pms_constrain_1: CORE_X_DRAM0_PMS_CONSTRAIN_1,
    core_0_dram0_pms_monitor_0: CORE_0_DRAM0_PMS_MONITOR_0,
    core_0_dram0_pms_monitor_1: CORE_0_DRAM0_PMS_MONITOR_1,
    core_0_dram0_pms_monitor_2: CORE_0_DRAM0_PMS_MONITOR_2,
    core_0_dram0_pms_monitor_3: CORE_0_DRAM0_PMS_MONITOR_3,
    core_0_pif_pms_constrain_0: CORE_0_PIF_PMS_CONSTRAIN_0,
    core_0_pif_pms_constrain_1: CORE_0_PIF_PMS_CONSTRAIN_1,
    core_0_pif_pms_constrain_2: CORE_0_PIF_PMS_CONSTRAIN_2,
    core_0_pif_pms_constrain_3: CORE_0_PIF_PMS_CONSTRAIN_3,
    core_0_pif_pms_constrain_4: CORE_0_PIF_PMS_CONSTRAIN_4,
    core_0_pif_pms_constrain_5: CORE_0_PIF_PMS_CONSTRAIN_5,
    core_0_pif_pms_constrain_6: CORE_0_PIF_PMS_CONSTRAIN_6,
    core_0_pif_pms_constrain_7: CORE_0_PIF_PMS_CONSTRAIN_7,
    core_0_pif_pms_constrain_8: CORE_0_PIF_PMS_CONSTRAIN_8,
    core_0_pif_pms_constrain_9: CORE_0_PIF_PMS_CONSTRAIN_9,
    core_0_pif_pms_constrain_10: CORE_0_PIF_PMS_CONSTRAIN_10,
    region_pms_constrain_0: REGION_PMS_CONSTRAIN_0,
    region_pms_constrain_1: REGION_PMS_CONSTRAIN_1,
    region_pms_constrain_2: REGION_PMS_CONSTRAIN_2,
    region_pms_constrain_3: REGION_PMS_CONSTRAIN_3,
    region_pms_constrain_4: REGION_PMS_CONSTRAIN_4,
    region_pms_constrain_5: REGION_PMS_CONSTRAIN_5,
    region_pms_constrain_6: REGION_PMS_CONSTRAIN_6,
    region_pms_constrain_7: REGION_PMS_CONSTRAIN_7,
    region_pms_constrain_8: REGION_PMS_CONSTRAIN_8,
    region_pms_constrain_9: REGION_PMS_CONSTRAIN_9,
    region_pms_constrain_10: REGION_PMS_CONSTRAIN_10,
    core_0_pif_pms_monitor_0: CORE_0_PIF_PMS_MONITOR_0,
    core_0_pif_pms_monitor_1: CORE_0_PIF_PMS_MONITOR_1,
    core_0_pif_pms_monitor_2: CORE_0_PIF_PMS_MONITOR_2,
    core_0_pif_pms_monitor_3: CORE_0_PIF_PMS_MONITOR_3,
    core_0_pif_pms_monitor_4: CORE_0_PIF_PMS_MONITOR_4,
    core_0_pif_pms_monitor_5: CORE_0_PIF_PMS_MONITOR_5,
    core_0_pif_pms_monitor_6: CORE_0_PIF_PMS_MONITOR_6,
    backup_bus_pms_constrain_0: BACKUP_BUS_PMS_CONSTRAIN_0,
    backup_bus_pms_constrain_1: BACKUP_BUS_PMS_CONSTRAIN_1,
    backup_bus_pms_constrain_2: BACKUP_BUS_PMS_CONSTRAIN_2,
    backup_bus_pms_constrain_3: BACKUP_BUS_PMS_CONSTRAIN_3,
    backup_bus_pms_constrain_4: BACKUP_BUS_PMS_CONSTRAIN_4,
    backup_bus_pms_monitor_0: BACKUP_BUS_PMS_MONITOR_0,
    backup_bus_pms_monitor_1: BACKUP_BUS_PMS_MONITOR_1,
    backup_bus_pms_monitor_2: BACKUP_BUS_PMS_MONITOR_2,
    backup_bus_pms_monitor_3: BACKUP_BUS_PMS_MONITOR_3,
    clock_gate: CLOCK_GATE,
    _reserved76: [u8; 0x0e88],
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - SENSITIVE_ROM_TABLE_LOCK_REG"]
    #[inline(always)]
    pub const fn rom_table_lock(&self) -> &ROM_TABLE_LOCK {
        &self.rom_table_lock
    }
    #[doc = "0x04 - SENSITIVE_ROM_TABLE_REG"]
    #[inline(always)]
    pub const fn rom_table(&self) -> &ROM_TABLE {
        &self.rom_table
    }
    #[doc = "0x08 - SENSITIVE_PRIVILEGE_MODE_SEL_LOCK_REG"]
    #[inline(always)]
    pub const fn privilege_mode_sel_lock(&self) -> &PRIVILEGE_MODE_SEL_LOCK {
        &self.privilege_mode_sel_lock
    }
    #[doc = "0x0c - SENSITIVE_PRIVILEGE_MODE_SEL_REG"]
    #[inline(always)]
    pub const fn privilege_mode_sel(&self) -> &PRIVILEGE_MODE_SEL {
        &self.privilege_mode_sel
    }
    #[doc = "0x10 - SENSITIVE_APB_PERIPHERAL_ACCESS_0_REG"]
    #[inline(always)]
    pub const fn apb_peripheral_access_0(&self) -> &APB_PERIPHERAL_ACCESS_0 {
        &self.apb_peripheral_access_0
    }
    #[doc = "0x14 - SENSITIVE_APB_PERIPHERAL_ACCESS_1_REG"]
    #[inline(always)]
    pub const fn apb_peripheral_access_1(&self) -> &APB_PERIPHERAL_ACCESS_1 {
        &self.apb_peripheral_access_1
    }
    #[doc = "0x18 - SENSITIVE_INTERNAL_SRAM_USAGE_0_REG"]
    #[inline(always)]
    pub const fn internal_sram_usage_0(&self) -> &INTERNAL_SRAM_USAGE_0 {
        &self.internal_sram_usage_0
    }
    #[doc = "0x1c - SENSITIVE_INTERNAL_SRAM_USAGE_1_REG"]
    #[inline(always)]
    pub const fn internal_sram_usage_1(&self) -> &INTERNAL_SRAM_USAGE_1 {
        &self.internal_sram_usage_1
    }
    #[doc = "0x20 - SENSITIVE_INTERNAL_SRAM_USAGE_3_REG"]
    #[inline(always)]
    pub const fn internal_sram_usage_3(&self) -> &INTERNAL_SRAM_USAGE_3 {
        &self.internal_sram_usage_3
    }
    #[doc = "0x24 - SENSITIVE_INTERNAL_SRAM_USAGE_4_REG"]
    #[inline(always)]
    pub const fn internal_sram_usage_4(&self) -> &INTERNAL_SRAM_USAGE_4 {
        &self.internal_sram_usage_4
    }
    #[doc = "0x28 - SENSITIVE_CACHE_TAG_ACCESS_0_REG"]
    #[inline(always)]
    pub const fn cache_tag_access_0(&self) -> &CACHE_TAG_ACCESS_0 {
        &self.cache_tag_access_0
    }
    #[doc = "0x2c - SENSITIVE_CACHE_TAG_ACCESS_1_REG"]
    #[inline(always)]
    pub const fn cache_tag_access_1(&self) -> &CACHE_TAG_ACCESS_1 {
        &self.cache_tag_access_1
    }
    #[doc = "0x30 - SENSITIVE_CACHE_MMU_ACCESS_0_REG"]
    #[inline(always)]
    pub const fn cache_mmu_access_0(&self) -> &CACHE_MMU_ACCESS_0 {
        &self.cache_mmu_access_0
    }
    #[doc = "0x34 - SENSITIVE_CACHE_MMU_ACCESS_1_REG"]
    #[inline(always)]
    pub const fn cache_mmu_access_1(&self) -> &CACHE_MMU_ACCESS_1 {
        &self.cache_mmu_access_1
    }
    #[doc = "0x38..0x80 - Cluster DMA_APBPERI%s, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is the index of cluster in the array. `n == 0` corresponds to `DMA_APBPERI_SPI2` cluster.</div>"]
    #[inline(always)]
    pub const fn dma_apbperi(&self, n: usize) -> &DMA_APBPERI {
        &self.dma_apbperi[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x38..0x80 - Cluster DMA_APBPERI%s, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
    #[inline(always)]
    pub fn dma_apbperi_iter(&self) -> impl Iterator<Item = &DMA_APBPERI> {
        self.dma_apbperi.iter()
    }
    #[doc = "0x38..0x40 - Cluster DMA_APBPERI_SPI2, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
    #[inline(always)]
    pub const fn dma_apbperi_spi2(&self) -> &DMA_APBPERI {
        self.dma_apbperi(0)
    }
    #[doc = "0x40..0x48 - Cluster DMA_APBPERI_UCHI0, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
    #[inline(always)]
    pub const fn dma_apbperi_uchi0(&self) -> &DMA_APBPERI {
        self.dma_apbperi(1)
    }
    #[doc = "0x48..0x50 - Cluster DMA_APBPERI_I2S0, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
    #[inline(always)]
    pub const fn dma_apbperi_i2s0(&self) -> &DMA_APBPERI {
        self.dma_apbperi(2)
    }
    #[doc = "0x50..0x58 - Cluster DMA_APBPERI_MAC, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
    #[inline(always)]
    pub const fn dma_apbperi_mac(&self) -> &DMA_APBPERI {
        self.dma_apbperi(3)
    }
    #[doc = "0x58..0x60 - Cluster DMA_APBPERI_BACKUP, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
    #[inline(always)]
    pub const fn dma_apbperi_backup(&self) -> &DMA_APBPERI {
        self.dma_apbperi(4)
    }
    #[doc = "0x60..0x68 - Cluster DMA_APBPERI_LC, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
    #[inline(always)]
    pub const fn dma_apbperi_lc(&self) -> &DMA_APBPERI {
        self.dma_apbperi(5)
    }
    #[doc = "0x68..0x70 - Cluster DMA_APBPERI_AES, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
    #[inline(always)]
    pub const fn dma_apbperi_aes(&self) -> &DMA_APBPERI {
        self.dma_apbperi(6)
    }
    #[doc = "0x70..0x78 - Cluster DMA_APBPERI_SHA, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
    #[inline(always)]
    pub const fn dma_apbperi_sha(&self) -> &DMA_APBPERI {
        self.dma_apbperi(7)
    }
    #[doc = "0x78..0x80 - Cluster DMA_APBPERI_ADC_DAC, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
    #[inline(always)]
    pub const fn dma_apbperi_adc_dac(&self) -> &DMA_APBPERI {
        self.dma_apbperi(8)
    }
    #[doc = "0x80 - SENSITIVE_DMA_APBPERI_PMS_MONITOR_0_REG"]
    #[inline(always)]
    pub const fn dma_apbperi_pms_monitor_0(&self) -> &DMA_APBPERI_PMS_MONITOR_0 {
        &self.dma_apbperi_pms_monitor_0
    }
    #[doc = "0x84 - SENSITIVE_DMA_APBPERI_PMS_MONITOR_1_REG"]
    #[inline(always)]
    pub const fn dma_apbperi_pms_monitor_1(&self) -> &DMA_APBPERI_PMS_MONITOR_1 {
        &self.dma_apbperi_pms_monitor_1
    }
    #[doc = "0x88 - SENSITIVE_DMA_APBPERI_PMS_MONITOR_2_REG"]
    #[inline(always)]
    pub const fn dma_apbperi_pms_monitor_2(&self) -> &DMA_APBPERI_PMS_MONITOR_2 {
        &self.dma_apbperi_pms_monitor_2
    }
    #[doc = "0x8c - SENSITIVE_DMA_APBPERI_PMS_MONITOR_3_REG"]
    #[inline(always)]
    pub const fn dma_apbperi_pms_monitor_3(&self) -> &DMA_APBPERI_PMS_MONITOR_3 {
        &self.dma_apbperi_pms_monitor_3
    }
    #[doc = "0x90 - SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_0_REG"]
    #[inline(always)]
    pub const fn core_x_iram0_dram0_dma_split_line_constrain_0(
        &self,
    ) -> &CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_0 {
        &self.core_x_iram0_dram0_dma_split_line_constrain_0
    }
    #[doc = "0x94 - SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_1_REG"]
    #[inline(always)]
    pub const fn core_x_iram0_dram0_dma_split_line_constrain_1(
        &self,
    ) -> &CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_1 {
        &self.core_x_iram0_dram0_dma_split_line_constrain_1
    }
    #[doc = "0x98 - SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_2_REG"]
    #[inline(always)]
    pub const fn core_x_iram0_dram0_dma_split_line_constrain_2(
        &self,
    ) -> &CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_2 {
        &self.core_x_iram0_dram0_dma_split_line_constrain_2
    }
    #[doc = "0x9c - SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_3_REG"]
    #[inline(always)]
    pub const fn core_x_iram0_dram0_dma_split_line_constrain_3(
        &self,
    ) -> &CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_3 {
        &self.core_x_iram0_dram0_dma_split_line_constrain_3
    }
    #[doc = "0xa0 - SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_4_REG"]
    #[inline(always)]
    pub const fn core_x_iram0_dram0_dma_split_line_constrain_4(
        &self,
    ) -> &CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_4 {
        &self.core_x_iram0_dram0_dma_split_line_constrain_4
    }
    #[doc = "0xa4 - SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_5_REG"]
    #[inline(always)]
    pub const fn core_x_iram0_dram0_dma_split_line_constrain_5(
        &self,
    ) -> &CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_5 {
        &self.core_x_iram0_dram0_dma_split_line_constrain_5
    }
    #[doc = "0xa8 - SENSITIVE_CORE_X_IRAM0_PMS_CONSTRAIN_0_REG"]
    #[inline(always)]
    pub const fn core_x_iram0_pms_constrain_0(&self) -> &CORE_X_IRAM0_PMS_CONSTRAIN_0 {
        &self.core_x_iram0_pms_constrain_0
    }
    #[doc = "0xac - SENSITIVE_CORE_X_IRAM0_PMS_CONSTRAIN_1_REG"]
    #[inline(always)]
    pub const fn core_x_iram0_pms_constrain_1(&self) -> &CORE_X_IRAM0_PMS_CONSTRAIN_1 {
        &self.core_x_iram0_pms_constrain_1
    }
    #[doc = "0xb0 - SENSITIVE_CORE_X_IRAM0_PMS_CONSTRAIN_2_REG"]
    #[inline(always)]
    pub const fn core_x_iram0_pms_constrain_2(&self) -> &CORE_X_IRAM0_PMS_CONSTRAIN_2 {
        &self.core_x_iram0_pms_constrain_2
    }
    #[doc = "0xb4 - SENSITIVE_CORE_0_IRAM0_PMS_MONITOR_0_REG"]
    #[inline(always)]
    pub const fn core_0_iram0_pms_monitor_0(&self) -> &CORE_0_IRAM0_PMS_MONITOR_0 {
        &self.core_0_iram0_pms_monitor_0
    }
    #[doc = "0xb8 - SENSITIVE_CORE_0_IRAM0_PMS_MONITOR_1_REG"]
    #[inline(always)]
    pub const fn core_0_iram0_pms_monitor_1(&self) -> &CORE_0_IRAM0_PMS_MONITOR_1 {
        &self.core_0_iram0_pms_monitor_1
    }
    #[doc = "0xbc - SENSITIVE_CORE_0_IRAM0_PMS_MONITOR_2_REG"]
    #[inline(always)]
    pub const fn core_0_iram0_pms_monitor_2(&self) -> &CORE_0_IRAM0_PMS_MONITOR_2 {
        &self.core_0_iram0_pms_monitor_2
    }
    #[doc = "0xc0 - SENSITIVE_CORE_X_DRAM0_PMS_CONSTRAIN_0_REG"]
    #[inline(always)]
    pub const fn core_x_dram0_pms_constrain_0(&self) -> &CORE_X_DRAM0_PMS_CONSTRAIN_0 {
        &self.core_x_dram0_pms_constrain_0
    }
    #[doc = "0xc4 - SENSITIVE_CORE_X_DRAM0_PMS_CONSTRAIN_1_REG"]
    #[inline(always)]
    pub const fn core_x_dram0_pms_constrain_1(&self) -> &CORE_X_DRAM0_PMS_CONSTRAIN_1 {
        &self.core_x_dram0_pms_constrain_1
    }
    #[doc = "0xc8 - SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_0_REG"]
    #[inline(always)]
    pub const fn core_0_dram0_pms_monitor_0(&self) -> &CORE_0_DRAM0_PMS_MONITOR_0 {
        &self.core_0_dram0_pms_monitor_0
    }
    #[doc = "0xcc - SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_1_REG"]
    #[inline(always)]
    pub const fn core_0_dram0_pms_monitor_1(&self) -> &CORE_0_DRAM0_PMS_MONITOR_1 {
        &self.core_0_dram0_pms_monitor_1
    }
    #[doc = "0xd0 - SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_2_REG"]
    #[inline(always)]
    pub const fn core_0_dram0_pms_monitor_2(&self) -> &CORE_0_DRAM0_PMS_MONITOR_2 {
        &self.core_0_dram0_pms_monitor_2
    }
    #[doc = "0xd4 - SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_3_REG"]
    #[inline(always)]
    pub const fn core_0_dram0_pms_monitor_3(&self) -> &CORE_0_DRAM0_PMS_MONITOR_3 {
        &self.core_0_dram0_pms_monitor_3
    }
    #[doc = "0xd8 - SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_0_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_constrain_0(&self) -> &CORE_0_PIF_PMS_CONSTRAIN_0 {
        &self.core_0_pif_pms_constrain_0
    }
    #[doc = "0xdc - SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_1_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_constrain_1(&self) -> &CORE_0_PIF_PMS_CONSTRAIN_1 {
        &self.core_0_pif_pms_constrain_1
    }
    #[doc = "0xe0 - SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_2_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_constrain_2(&self) -> &CORE_0_PIF_PMS_CONSTRAIN_2 {
        &self.core_0_pif_pms_constrain_2
    }
    #[doc = "0xe4 - SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_3_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_constrain_3(&self) -> &CORE_0_PIF_PMS_CONSTRAIN_3 {
        &self.core_0_pif_pms_constrain_3
    }
    #[doc = "0xe8 - SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_4_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_constrain_4(&self) -> &CORE_0_PIF_PMS_CONSTRAIN_4 {
        &self.core_0_pif_pms_constrain_4
    }
    #[doc = "0xec - SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_5_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_constrain_5(&self) -> &CORE_0_PIF_PMS_CONSTRAIN_5 {
        &self.core_0_pif_pms_constrain_5
    }
    #[doc = "0xf0 - SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_6_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_constrain_6(&self) -> &CORE_0_PIF_PMS_CONSTRAIN_6 {
        &self.core_0_pif_pms_constrain_6
    }
    #[doc = "0xf4 - SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_7_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_constrain_7(&self) -> &CORE_0_PIF_PMS_CONSTRAIN_7 {
        &self.core_0_pif_pms_constrain_7
    }
    #[doc = "0xf8 - SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_8_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_constrain_8(&self) -> &CORE_0_PIF_PMS_CONSTRAIN_8 {
        &self.core_0_pif_pms_constrain_8
    }
    #[doc = "0xfc - SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_9_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_constrain_9(&self) -> &CORE_0_PIF_PMS_CONSTRAIN_9 {
        &self.core_0_pif_pms_constrain_9
    }
    #[doc = "0x100 - SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_10_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_constrain_10(&self) -> &CORE_0_PIF_PMS_CONSTRAIN_10 {
        &self.core_0_pif_pms_constrain_10
    }
    #[doc = "0x104 - SENSITIVE_REGION_PMS_CONSTRAIN_0_REG"]
    #[inline(always)]
    pub const fn region_pms_constrain_0(&self) -> &REGION_PMS_CONSTRAIN_0 {
        &self.region_pms_constrain_0
    }
    #[doc = "0x108 - SENSITIVE_REGION_PMS_CONSTRAIN_1_REG"]
    #[inline(always)]
    pub const fn region_pms_constrain_1(&self) -> &REGION_PMS_CONSTRAIN_1 {
        &self.region_pms_constrain_1
    }
    #[doc = "0x10c - SENSITIVE_REGION_PMS_CONSTRAIN_2_REG"]
    #[inline(always)]
    pub const fn region_pms_constrain_2(&self) -> &REGION_PMS_CONSTRAIN_2 {
        &self.region_pms_constrain_2
    }
    #[doc = "0x110 - SENSITIVE_REGION_PMS_CONSTRAIN_3_REG"]
    #[inline(always)]
    pub const fn region_pms_constrain_3(&self) -> &REGION_PMS_CONSTRAIN_3 {
        &self.region_pms_constrain_3
    }
    #[doc = "0x114 - SENSITIVE_REGION_PMS_CONSTRAIN_4_REG"]
    #[inline(always)]
    pub const fn region_pms_constrain_4(&self) -> &REGION_PMS_CONSTRAIN_4 {
        &self.region_pms_constrain_4
    }
    #[doc = "0x118 - SENSITIVE_REGION_PMS_CONSTRAIN_5_REG"]
    #[inline(always)]
    pub const fn region_pms_constrain_5(&self) -> &REGION_PMS_CONSTRAIN_5 {
        &self.region_pms_constrain_5
    }
    #[doc = "0x11c - SENSITIVE_REGION_PMS_CONSTRAIN_6_REG"]
    #[inline(always)]
    pub const fn region_pms_constrain_6(&self) -> &REGION_PMS_CONSTRAIN_6 {
        &self.region_pms_constrain_6
    }
    #[doc = "0x120 - SENSITIVE_REGION_PMS_CONSTRAIN_7_REG"]
    #[inline(always)]
    pub const fn region_pms_constrain_7(&self) -> &REGION_PMS_CONSTRAIN_7 {
        &self.region_pms_constrain_7
    }
    #[doc = "0x124 - SENSITIVE_REGION_PMS_CONSTRAIN_8_REG"]
    #[inline(always)]
    pub const fn region_pms_constrain_8(&self) -> &REGION_PMS_CONSTRAIN_8 {
        &self.region_pms_constrain_8
    }
    #[doc = "0x128 - SENSITIVE_REGION_PMS_CONSTRAIN_9_REG"]
    #[inline(always)]
    pub const fn region_pms_constrain_9(&self) -> &REGION_PMS_CONSTRAIN_9 {
        &self.region_pms_constrain_9
    }
    #[doc = "0x12c - SENSITIVE_REGION_PMS_CONSTRAIN_10_REG"]
    #[inline(always)]
    pub const fn region_pms_constrain_10(&self) -> &REGION_PMS_CONSTRAIN_10 {
        &self.region_pms_constrain_10
    }
    #[doc = "0x130 - SENSITIVE_CORE_0_PIF_PMS_MONITOR_0_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_monitor_0(&self) -> &CORE_0_PIF_PMS_MONITOR_0 {
        &self.core_0_pif_pms_monitor_0
    }
    #[doc = "0x134 - SENSITIVE_CORE_0_PIF_PMS_MONITOR_1_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_monitor_1(&self) -> &CORE_0_PIF_PMS_MONITOR_1 {
        &self.core_0_pif_pms_monitor_1
    }
    #[doc = "0x138 - SENSITIVE_CORE_0_PIF_PMS_MONITOR_2_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_monitor_2(&self) -> &CORE_0_PIF_PMS_MONITOR_2 {
        &self.core_0_pif_pms_monitor_2
    }
    #[doc = "0x13c - SENSITIVE_CORE_0_PIF_PMS_MONITOR_3_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_monitor_3(&self) -> &CORE_0_PIF_PMS_MONITOR_3 {
        &self.core_0_pif_pms_monitor_3
    }
    #[doc = "0x140 - SENSITIVE_CORE_0_PIF_PMS_MONITOR_4_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_monitor_4(&self) -> &CORE_0_PIF_PMS_MONITOR_4 {
        &self.core_0_pif_pms_monitor_4
    }
    #[doc = "0x144 - SENSITIVE_CORE_0_PIF_PMS_MONITOR_5_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_monitor_5(&self) -> &CORE_0_PIF_PMS_MONITOR_5 {
        &self.core_0_pif_pms_monitor_5
    }
    #[doc = "0x148 - SENSITIVE_CORE_0_PIF_PMS_MONITOR_6_REG"]
    #[inline(always)]
    pub const fn core_0_pif_pms_monitor_6(&self) -> &CORE_0_PIF_PMS_MONITOR_6 {
        &self.core_0_pif_pms_monitor_6
    }
    #[doc = "0x14c - SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_0_REG"]
    #[inline(always)]
    pub const fn backup_bus_pms_constrain_0(&self) -> &BACKUP_BUS_PMS_CONSTRAIN_0 {
        &self.backup_bus_pms_constrain_0
    }
    #[doc = "0x150 - SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_1_REG"]
    #[inline(always)]
    pub const fn backup_bus_pms_constrain_1(&self) -> &BACKUP_BUS_PMS_CONSTRAIN_1 {
        &self.backup_bus_pms_constrain_1
    }
    #[doc = "0x154 - SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_2_REG"]
    #[inline(always)]
    pub const fn backup_bus_pms_constrain_2(&self) -> &BACKUP_BUS_PMS_CONSTRAIN_2 {
        &self.backup_bus_pms_constrain_2
    }
    #[doc = "0x158 - SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_3_REG"]
    #[inline(always)]
    pub const fn backup_bus_pms_constrain_3(&self) -> &BACKUP_BUS_PMS_CONSTRAIN_3 {
        &self.backup_bus_pms_constrain_3
    }
    #[doc = "0x15c - SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_4_REG"]
    #[inline(always)]
    pub const fn backup_bus_pms_constrain_4(&self) -> &BACKUP_BUS_PMS_CONSTRAIN_4 {
        &self.backup_bus_pms_constrain_4
    }
    #[doc = "0x160 - SENSITIVE_BACKUP_BUS_PMS_MONITOR_0_REG"]
    #[inline(always)]
    pub const fn backup_bus_pms_monitor_0(&self) -> &BACKUP_BUS_PMS_MONITOR_0 {
        &self.backup_bus_pms_monitor_0
    }
    #[doc = "0x164 - SENSITIVE_BACKUP_BUS_PMS_MONITOR_1_REG"]
    #[inline(always)]
    pub const fn backup_bus_pms_monitor_1(&self) -> &BACKUP_BUS_PMS_MONITOR_1 {
        &self.backup_bus_pms_monitor_1
    }
    #[doc = "0x168 - SENSITIVE_BACKUP_BUS_PMS_MONITOR_2_REG"]
    #[inline(always)]
    pub const fn backup_bus_pms_monitor_2(&self) -> &BACKUP_BUS_PMS_MONITOR_2 {
        &self.backup_bus_pms_monitor_2
    }
    #[doc = "0x16c - SENSITIVE_BACKUP_BUS_PMS_MONITOR_3_REG"]
    #[inline(always)]
    pub const fn backup_bus_pms_monitor_3(&self) -> &BACKUP_BUS_PMS_MONITOR_3 {
        &self.backup_bus_pms_monitor_3
    }
    #[doc = "0x170 - SENSITIVE_CLOCK_GATE_REG"]
    #[inline(always)]
    pub const fn clock_gate(&self) -> &CLOCK_GATE {
        &self.clock_gate
    }
    #[doc = "0xffc - SENSITIVE_DATE_REG"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "ROM_TABLE_LOCK (rw) register accessor: SENSITIVE_ROM_TABLE_LOCK_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`rom_table_lock::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rom_table_lock::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rom_table_lock`] module"]
pub type ROM_TABLE_LOCK = crate::Reg<rom_table_lock::ROM_TABLE_LOCK_SPEC>;
#[doc = "SENSITIVE_ROM_TABLE_LOCK_REG"]
pub mod rom_table_lock;
#[doc = "ROM_TABLE (rw) register accessor: SENSITIVE_ROM_TABLE_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`rom_table::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rom_table::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rom_table`] module"]
pub type ROM_TABLE = crate::Reg<rom_table::ROM_TABLE_SPEC>;
#[doc = "SENSITIVE_ROM_TABLE_REG"]
pub mod rom_table;
#[doc = "PRIVILEGE_MODE_SEL_LOCK (rw) register accessor: SENSITIVE_PRIVILEGE_MODE_SEL_LOCK_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`privilege_mode_sel_lock::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`privilege_mode_sel_lock::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@privilege_mode_sel_lock`] module"]
pub type PRIVILEGE_MODE_SEL_LOCK =
    crate::Reg<privilege_mode_sel_lock::PRIVILEGE_MODE_SEL_LOCK_SPEC>;
#[doc = "SENSITIVE_PRIVILEGE_MODE_SEL_LOCK_REG"]
pub mod privilege_mode_sel_lock;
#[doc = "PRIVILEGE_MODE_SEL (rw) register accessor: SENSITIVE_PRIVILEGE_MODE_SEL_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`privilege_mode_sel::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`privilege_mode_sel::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@privilege_mode_sel`] module"]
pub type PRIVILEGE_MODE_SEL = crate::Reg<privilege_mode_sel::PRIVILEGE_MODE_SEL_SPEC>;
#[doc = "SENSITIVE_PRIVILEGE_MODE_SEL_REG"]
pub mod privilege_mode_sel;
#[doc = "APB_PERIPHERAL_ACCESS_0 (rw) register accessor: SENSITIVE_APB_PERIPHERAL_ACCESS_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`apb_peripheral_access_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`apb_peripheral_access_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@apb_peripheral_access_0`] module"]
pub type APB_PERIPHERAL_ACCESS_0 =
    crate::Reg<apb_peripheral_access_0::APB_PERIPHERAL_ACCESS_0_SPEC>;
#[doc = "SENSITIVE_APB_PERIPHERAL_ACCESS_0_REG"]
pub mod apb_peripheral_access_0;
#[doc = "APB_PERIPHERAL_ACCESS_1 (rw) register accessor: SENSITIVE_APB_PERIPHERAL_ACCESS_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`apb_peripheral_access_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`apb_peripheral_access_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@apb_peripheral_access_1`] module"]
pub type APB_PERIPHERAL_ACCESS_1 =
    crate::Reg<apb_peripheral_access_1::APB_PERIPHERAL_ACCESS_1_SPEC>;
#[doc = "SENSITIVE_APB_PERIPHERAL_ACCESS_1_REG"]
pub mod apb_peripheral_access_1;
#[doc = "INTERNAL_SRAM_USAGE_0 (rw) register accessor: SENSITIVE_INTERNAL_SRAM_USAGE_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`internal_sram_usage_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`internal_sram_usage_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@internal_sram_usage_0`] module"]
pub type INTERNAL_SRAM_USAGE_0 = crate::Reg<internal_sram_usage_0::INTERNAL_SRAM_USAGE_0_SPEC>;
#[doc = "SENSITIVE_INTERNAL_SRAM_USAGE_0_REG"]
pub mod internal_sram_usage_0;
#[doc = "INTERNAL_SRAM_USAGE_1 (rw) register accessor: SENSITIVE_INTERNAL_SRAM_USAGE_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`internal_sram_usage_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`internal_sram_usage_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@internal_sram_usage_1`] module"]
pub type INTERNAL_SRAM_USAGE_1 = crate::Reg<internal_sram_usage_1::INTERNAL_SRAM_USAGE_1_SPEC>;
#[doc = "SENSITIVE_INTERNAL_SRAM_USAGE_1_REG"]
pub mod internal_sram_usage_1;
#[doc = "INTERNAL_SRAM_USAGE_3 (rw) register accessor: SENSITIVE_INTERNAL_SRAM_USAGE_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`internal_sram_usage_3::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`internal_sram_usage_3::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@internal_sram_usage_3`] module"]
pub type INTERNAL_SRAM_USAGE_3 = crate::Reg<internal_sram_usage_3::INTERNAL_SRAM_USAGE_3_SPEC>;
#[doc = "SENSITIVE_INTERNAL_SRAM_USAGE_3_REG"]
pub mod internal_sram_usage_3;
#[doc = "INTERNAL_SRAM_USAGE_4 (rw) register accessor: SENSITIVE_INTERNAL_SRAM_USAGE_4_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`internal_sram_usage_4::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`internal_sram_usage_4::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@internal_sram_usage_4`] module"]
pub type INTERNAL_SRAM_USAGE_4 = crate::Reg<internal_sram_usage_4::INTERNAL_SRAM_USAGE_4_SPEC>;
#[doc = "SENSITIVE_INTERNAL_SRAM_USAGE_4_REG"]
pub mod internal_sram_usage_4;
#[doc = "CACHE_TAG_ACCESS_0 (rw) register accessor: SENSITIVE_CACHE_TAG_ACCESS_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_tag_access_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_tag_access_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_tag_access_0`] module"]
pub type CACHE_TAG_ACCESS_0 = crate::Reg<cache_tag_access_0::CACHE_TAG_ACCESS_0_SPEC>;
#[doc = "SENSITIVE_CACHE_TAG_ACCESS_0_REG"]
pub mod cache_tag_access_0;
#[doc = "CACHE_TAG_ACCESS_1 (rw) register accessor: SENSITIVE_CACHE_TAG_ACCESS_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_tag_access_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_tag_access_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_tag_access_1`] module"]
pub type CACHE_TAG_ACCESS_1 = crate::Reg<cache_tag_access_1::CACHE_TAG_ACCESS_1_SPEC>;
#[doc = "SENSITIVE_CACHE_TAG_ACCESS_1_REG"]
pub mod cache_tag_access_1;
#[doc = "CACHE_MMU_ACCESS_0 (rw) register accessor: SENSITIVE_CACHE_MMU_ACCESS_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_mmu_access_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_mmu_access_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_mmu_access_0`] module"]
pub type CACHE_MMU_ACCESS_0 = crate::Reg<cache_mmu_access_0::CACHE_MMU_ACCESS_0_SPEC>;
#[doc = "SENSITIVE_CACHE_MMU_ACCESS_0_REG"]
pub mod cache_mmu_access_0;
#[doc = "CACHE_MMU_ACCESS_1 (rw) register accessor: SENSITIVE_CACHE_MMU_ACCESS_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_mmu_access_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_mmu_access_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_mmu_access_1`] module"]
pub type CACHE_MMU_ACCESS_1 = crate::Reg<cache_mmu_access_1::CACHE_MMU_ACCESS_1_SPEC>;
#[doc = "SENSITIVE_CACHE_MMU_ACCESS_1_REG"]
pub mod cache_mmu_access_1;
#[doc = "Cluster DMA_APBPERI%s, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
pub use self::dma_apbperi::DMA_APBPERI;
#[doc = r"Cluster"]
#[doc = "Cluster DMA_APBPERI%s, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
pub mod dma_apbperi;
#[doc = "DMA_APBPERI_PMS_MONITOR_0 (rw) register accessor: SENSITIVE_DMA_APBPERI_PMS_MONITOR_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`dma_apbperi_pms_monitor_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_apbperi_pms_monitor_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_apbperi_pms_monitor_0`] module"]
pub type DMA_APBPERI_PMS_MONITOR_0 =
    crate::Reg<dma_apbperi_pms_monitor_0::DMA_APBPERI_PMS_MONITOR_0_SPEC>;
#[doc = "SENSITIVE_DMA_APBPERI_PMS_MONITOR_0_REG"]
pub mod dma_apbperi_pms_monitor_0;
#[doc = "DMA_APBPERI_PMS_MONITOR_1 (rw) register accessor: SENSITIVE_DMA_APBPERI_PMS_MONITOR_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`dma_apbperi_pms_monitor_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_apbperi_pms_monitor_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_apbperi_pms_monitor_1`] module"]
pub type DMA_APBPERI_PMS_MONITOR_1 =
    crate::Reg<dma_apbperi_pms_monitor_1::DMA_APBPERI_PMS_MONITOR_1_SPEC>;
#[doc = "SENSITIVE_DMA_APBPERI_PMS_MONITOR_1_REG"]
pub mod dma_apbperi_pms_monitor_1;
#[doc = "DMA_APBPERI_PMS_MONITOR_2 (r) register accessor: SENSITIVE_DMA_APBPERI_PMS_MONITOR_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`dma_apbperi_pms_monitor_2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_apbperi_pms_monitor_2`] module"]
pub type DMA_APBPERI_PMS_MONITOR_2 =
    crate::Reg<dma_apbperi_pms_monitor_2::DMA_APBPERI_PMS_MONITOR_2_SPEC>;
#[doc = "SENSITIVE_DMA_APBPERI_PMS_MONITOR_2_REG"]
pub mod dma_apbperi_pms_monitor_2;
#[doc = "DMA_APBPERI_PMS_MONITOR_3 (r) register accessor: SENSITIVE_DMA_APBPERI_PMS_MONITOR_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`dma_apbperi_pms_monitor_3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_apbperi_pms_monitor_3`] module"]
pub type DMA_APBPERI_PMS_MONITOR_3 =
    crate::Reg<dma_apbperi_pms_monitor_3::DMA_APBPERI_PMS_MONITOR_3_SPEC>;
#[doc = "SENSITIVE_DMA_APBPERI_PMS_MONITOR_3_REG"]
pub mod dma_apbperi_pms_monitor_3;
#[doc = "CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_0 (rw) register accessor: SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_x_iram0_dram0_dma_split_line_constrain_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_x_iram0_dram0_dma_split_line_constrain_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_x_iram0_dram0_dma_split_line_constrain_0`] module"]
pub type CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_0 = crate :: Reg < core_x_iram0_dram0_dma_split_line_constrain_0 :: CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_0_SPEC > ;
#[doc = "SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_0_REG"]
pub mod core_x_iram0_dram0_dma_split_line_constrain_0;
#[doc = "CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_1 (rw) register accessor: SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_x_iram0_dram0_dma_split_line_constrain_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_x_iram0_dram0_dma_split_line_constrain_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_x_iram0_dram0_dma_split_line_constrain_1`] module"]
pub type CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_1 = crate :: Reg < core_x_iram0_dram0_dma_split_line_constrain_1 :: CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_1_SPEC > ;
#[doc = "SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_1_REG"]
pub mod core_x_iram0_dram0_dma_split_line_constrain_1;
#[doc = "CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_2 (rw) register accessor: SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_x_iram0_dram0_dma_split_line_constrain_2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_x_iram0_dram0_dma_split_line_constrain_2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_x_iram0_dram0_dma_split_line_constrain_2`] module"]
pub type CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_2 = crate :: Reg < core_x_iram0_dram0_dma_split_line_constrain_2 :: CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_2_SPEC > ;
#[doc = "SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_2_REG"]
pub mod core_x_iram0_dram0_dma_split_line_constrain_2;
#[doc = "CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_3 (rw) register accessor: SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_x_iram0_dram0_dma_split_line_constrain_3::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_x_iram0_dram0_dma_split_line_constrain_3::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_x_iram0_dram0_dma_split_line_constrain_3`] module"]
pub type CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_3 = crate :: Reg < core_x_iram0_dram0_dma_split_line_constrain_3 :: CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_3_SPEC > ;
#[doc = "SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_3_REG"]
pub mod core_x_iram0_dram0_dma_split_line_constrain_3;
#[doc = "CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_4 (rw) register accessor: SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_4_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_x_iram0_dram0_dma_split_line_constrain_4::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_x_iram0_dram0_dma_split_line_constrain_4::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_x_iram0_dram0_dma_split_line_constrain_4`] module"]
pub type CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_4 = crate :: Reg < core_x_iram0_dram0_dma_split_line_constrain_4 :: CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_4_SPEC > ;
#[doc = "SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_4_REG"]
pub mod core_x_iram0_dram0_dma_split_line_constrain_4;
#[doc = "CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_5 (rw) register accessor: SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_5_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_x_iram0_dram0_dma_split_line_constrain_5::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_x_iram0_dram0_dma_split_line_constrain_5::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_x_iram0_dram0_dma_split_line_constrain_5`] module"]
pub type CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_5 = crate :: Reg < core_x_iram0_dram0_dma_split_line_constrain_5 :: CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_5_SPEC > ;
#[doc = "SENSITIVE_CORE_X_IRAM0_DRAM0_DMA_SPLIT_LINE_CONSTRAIN_5_REG"]
pub mod core_x_iram0_dram0_dma_split_line_constrain_5;
#[doc = "CORE_X_IRAM0_PMS_CONSTRAIN_0 (rw) register accessor: SENSITIVE_CORE_X_IRAM0_PMS_CONSTRAIN_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_x_iram0_pms_constrain_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_x_iram0_pms_constrain_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_x_iram0_pms_constrain_0`] module"]
pub type CORE_X_IRAM0_PMS_CONSTRAIN_0 =
    crate::Reg<core_x_iram0_pms_constrain_0::CORE_X_IRAM0_PMS_CONSTRAIN_0_SPEC>;
#[doc = "SENSITIVE_CORE_X_IRAM0_PMS_CONSTRAIN_0_REG"]
pub mod core_x_iram0_pms_constrain_0;
#[doc = "CORE_X_IRAM0_PMS_CONSTRAIN_1 (rw) register accessor: SENSITIVE_CORE_X_IRAM0_PMS_CONSTRAIN_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_x_iram0_pms_constrain_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_x_iram0_pms_constrain_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_x_iram0_pms_constrain_1`] module"]
pub type CORE_X_IRAM0_PMS_CONSTRAIN_1 =
    crate::Reg<core_x_iram0_pms_constrain_1::CORE_X_IRAM0_PMS_CONSTRAIN_1_SPEC>;
#[doc = "SENSITIVE_CORE_X_IRAM0_PMS_CONSTRAIN_1_REG"]
pub mod core_x_iram0_pms_constrain_1;
#[doc = "CORE_X_IRAM0_PMS_CONSTRAIN_2 (rw) register accessor: SENSITIVE_CORE_X_IRAM0_PMS_CONSTRAIN_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_x_iram0_pms_constrain_2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_x_iram0_pms_constrain_2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_x_iram0_pms_constrain_2`] module"]
pub type CORE_X_IRAM0_PMS_CONSTRAIN_2 =
    crate::Reg<core_x_iram0_pms_constrain_2::CORE_X_IRAM0_PMS_CONSTRAIN_2_SPEC>;
#[doc = "SENSITIVE_CORE_X_IRAM0_PMS_CONSTRAIN_2_REG"]
pub mod core_x_iram0_pms_constrain_2;
#[doc = "CORE_0_IRAM0_PMS_MONITOR_0 (rw) register accessor: SENSITIVE_CORE_0_IRAM0_PMS_MONITOR_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_iram0_pms_monitor_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_iram0_pms_monitor_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_iram0_pms_monitor_0`] module"]
pub type CORE_0_IRAM0_PMS_MONITOR_0 =
    crate::Reg<core_0_iram0_pms_monitor_0::CORE_0_IRAM0_PMS_MONITOR_0_SPEC>;
#[doc = "SENSITIVE_CORE_0_IRAM0_PMS_MONITOR_0_REG"]
pub mod core_0_iram0_pms_monitor_0;
#[doc = "CORE_0_IRAM0_PMS_MONITOR_1 (rw) register accessor: SENSITIVE_CORE_0_IRAM0_PMS_MONITOR_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_iram0_pms_monitor_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_iram0_pms_monitor_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_iram0_pms_monitor_1`] module"]
pub type CORE_0_IRAM0_PMS_MONITOR_1 =
    crate::Reg<core_0_iram0_pms_monitor_1::CORE_0_IRAM0_PMS_MONITOR_1_SPEC>;
#[doc = "SENSITIVE_CORE_0_IRAM0_PMS_MONITOR_1_REG"]
pub mod core_0_iram0_pms_monitor_1;
#[doc = "CORE_0_IRAM0_PMS_MONITOR_2 (r) register accessor: SENSITIVE_CORE_0_IRAM0_PMS_MONITOR_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_iram0_pms_monitor_2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_iram0_pms_monitor_2`] module"]
pub type CORE_0_IRAM0_PMS_MONITOR_2 =
    crate::Reg<core_0_iram0_pms_monitor_2::CORE_0_IRAM0_PMS_MONITOR_2_SPEC>;
#[doc = "SENSITIVE_CORE_0_IRAM0_PMS_MONITOR_2_REG"]
pub mod core_0_iram0_pms_monitor_2;
#[doc = "CORE_X_DRAM0_PMS_CONSTRAIN_0 (rw) register accessor: SENSITIVE_CORE_X_DRAM0_PMS_CONSTRAIN_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_x_dram0_pms_constrain_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_x_dram0_pms_constrain_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_x_dram0_pms_constrain_0`] module"]
pub type CORE_X_DRAM0_PMS_CONSTRAIN_0 =
    crate::Reg<core_x_dram0_pms_constrain_0::CORE_X_DRAM0_PMS_CONSTRAIN_0_SPEC>;
#[doc = "SENSITIVE_CORE_X_DRAM0_PMS_CONSTRAIN_0_REG"]
pub mod core_x_dram0_pms_constrain_0;
#[doc = "CORE_X_DRAM0_PMS_CONSTRAIN_1 (rw) register accessor: SENSITIVE_CORE_X_DRAM0_PMS_CONSTRAIN_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_x_dram0_pms_constrain_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_x_dram0_pms_constrain_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_x_dram0_pms_constrain_1`] module"]
pub type CORE_X_DRAM0_PMS_CONSTRAIN_1 =
    crate::Reg<core_x_dram0_pms_constrain_1::CORE_X_DRAM0_PMS_CONSTRAIN_1_SPEC>;
#[doc = "SENSITIVE_CORE_X_DRAM0_PMS_CONSTRAIN_1_REG"]
pub mod core_x_dram0_pms_constrain_1;
#[doc = "CORE_0_DRAM0_PMS_MONITOR_0 (rw) register accessor: SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_dram0_pms_monitor_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_dram0_pms_monitor_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_dram0_pms_monitor_0`] module"]
pub type CORE_0_DRAM0_PMS_MONITOR_0 =
    crate::Reg<core_0_dram0_pms_monitor_0::CORE_0_DRAM0_PMS_MONITOR_0_SPEC>;
#[doc = "SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_0_REG"]
pub mod core_0_dram0_pms_monitor_0;
#[doc = "CORE_0_DRAM0_PMS_MONITOR_1 (rw) register accessor: SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_dram0_pms_monitor_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_dram0_pms_monitor_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_dram0_pms_monitor_1`] module"]
pub type CORE_0_DRAM0_PMS_MONITOR_1 =
    crate::Reg<core_0_dram0_pms_monitor_1::CORE_0_DRAM0_PMS_MONITOR_1_SPEC>;
#[doc = "SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_1_REG"]
pub mod core_0_dram0_pms_monitor_1;
#[doc = "CORE_0_DRAM0_PMS_MONITOR_2 (r) register accessor: SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_dram0_pms_monitor_2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_dram0_pms_monitor_2`] module"]
pub type CORE_0_DRAM0_PMS_MONITOR_2 =
    crate::Reg<core_0_dram0_pms_monitor_2::CORE_0_DRAM0_PMS_MONITOR_2_SPEC>;
#[doc = "SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_2_REG"]
pub mod core_0_dram0_pms_monitor_2;
#[doc = "CORE_0_DRAM0_PMS_MONITOR_3 (r) register accessor: SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_dram0_pms_monitor_3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_dram0_pms_monitor_3`] module"]
pub type CORE_0_DRAM0_PMS_MONITOR_3 =
    crate::Reg<core_0_dram0_pms_monitor_3::CORE_0_DRAM0_PMS_MONITOR_3_SPEC>;
#[doc = "SENSITIVE_CORE_0_DRAM0_PMS_MONITOR_3_REG"]
pub mod core_0_dram0_pms_monitor_3;
#[doc = "CORE_0_PIF_PMS_CONSTRAIN_0 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_constrain_0`] module"]
pub type CORE_0_PIF_PMS_CONSTRAIN_0 =
    crate::Reg<core_0_pif_pms_constrain_0::CORE_0_PIF_PMS_CONSTRAIN_0_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_0_REG"]
pub mod core_0_pif_pms_constrain_0;
#[doc = "CORE_0_PIF_PMS_CONSTRAIN_1 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_constrain_1`] module"]
pub type CORE_0_PIF_PMS_CONSTRAIN_1 =
    crate::Reg<core_0_pif_pms_constrain_1::CORE_0_PIF_PMS_CONSTRAIN_1_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_1_REG"]
pub mod core_0_pif_pms_constrain_1;
#[doc = "CORE_0_PIF_PMS_CONSTRAIN_2 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_constrain_2`] module"]
pub type CORE_0_PIF_PMS_CONSTRAIN_2 =
    crate::Reg<core_0_pif_pms_constrain_2::CORE_0_PIF_PMS_CONSTRAIN_2_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_2_REG"]
pub mod core_0_pif_pms_constrain_2;
#[doc = "CORE_0_PIF_PMS_CONSTRAIN_3 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_3::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_3::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_constrain_3`] module"]
pub type CORE_0_PIF_PMS_CONSTRAIN_3 =
    crate::Reg<core_0_pif_pms_constrain_3::CORE_0_PIF_PMS_CONSTRAIN_3_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_3_REG"]
pub mod core_0_pif_pms_constrain_3;
#[doc = "CORE_0_PIF_PMS_CONSTRAIN_4 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_4_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_4::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_4::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_constrain_4`] module"]
pub type CORE_0_PIF_PMS_CONSTRAIN_4 =
    crate::Reg<core_0_pif_pms_constrain_4::CORE_0_PIF_PMS_CONSTRAIN_4_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_4_REG"]
pub mod core_0_pif_pms_constrain_4;
#[doc = "CORE_0_PIF_PMS_CONSTRAIN_5 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_5_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_5::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_5::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_constrain_5`] module"]
pub type CORE_0_PIF_PMS_CONSTRAIN_5 =
    crate::Reg<core_0_pif_pms_constrain_5::CORE_0_PIF_PMS_CONSTRAIN_5_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_5_REG"]
pub mod core_0_pif_pms_constrain_5;
#[doc = "CORE_0_PIF_PMS_CONSTRAIN_6 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_6_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_6::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_6::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_constrain_6`] module"]
pub type CORE_0_PIF_PMS_CONSTRAIN_6 =
    crate::Reg<core_0_pif_pms_constrain_6::CORE_0_PIF_PMS_CONSTRAIN_6_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_6_REG"]
pub mod core_0_pif_pms_constrain_6;
#[doc = "CORE_0_PIF_PMS_CONSTRAIN_7 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_7_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_7::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_7::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_constrain_7`] module"]
pub type CORE_0_PIF_PMS_CONSTRAIN_7 =
    crate::Reg<core_0_pif_pms_constrain_7::CORE_0_PIF_PMS_CONSTRAIN_7_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_7_REG"]
pub mod core_0_pif_pms_constrain_7;
#[doc = "CORE_0_PIF_PMS_CONSTRAIN_8 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_8_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_8::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_8::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_constrain_8`] module"]
pub type CORE_0_PIF_PMS_CONSTRAIN_8 =
    crate::Reg<core_0_pif_pms_constrain_8::CORE_0_PIF_PMS_CONSTRAIN_8_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_8_REG"]
pub mod core_0_pif_pms_constrain_8;
#[doc = "CORE_0_PIF_PMS_CONSTRAIN_9 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_9_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_9::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_9::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_constrain_9`] module"]
pub type CORE_0_PIF_PMS_CONSTRAIN_9 =
    crate::Reg<core_0_pif_pms_constrain_9::CORE_0_PIF_PMS_CONSTRAIN_9_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_9_REG"]
pub mod core_0_pif_pms_constrain_9;
#[doc = "CORE_0_PIF_PMS_CONSTRAIN_10 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_10_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_10::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_10::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_constrain_10`] module"]
pub type CORE_0_PIF_PMS_CONSTRAIN_10 =
    crate::Reg<core_0_pif_pms_constrain_10::CORE_0_PIF_PMS_CONSTRAIN_10_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_10_REG"]
pub mod core_0_pif_pms_constrain_10;
#[doc = "REGION_PMS_CONSTRAIN_0 (rw) register accessor: SENSITIVE_REGION_PMS_CONSTRAIN_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@region_pms_constrain_0`] module"]
pub type REGION_PMS_CONSTRAIN_0 = crate::Reg<region_pms_constrain_0::REGION_PMS_CONSTRAIN_0_SPEC>;
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_0_REG"]
pub mod region_pms_constrain_0;
#[doc = "REGION_PMS_CONSTRAIN_1 (rw) register accessor: SENSITIVE_REGION_PMS_CONSTRAIN_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@region_pms_constrain_1`] module"]
pub type REGION_PMS_CONSTRAIN_1 = crate::Reg<region_pms_constrain_1::REGION_PMS_CONSTRAIN_1_SPEC>;
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_1_REG"]
pub mod region_pms_constrain_1;
#[doc = "REGION_PMS_CONSTRAIN_2 (rw) register accessor: SENSITIVE_REGION_PMS_CONSTRAIN_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@region_pms_constrain_2`] module"]
pub type REGION_PMS_CONSTRAIN_2 = crate::Reg<region_pms_constrain_2::REGION_PMS_CONSTRAIN_2_SPEC>;
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_2_REG"]
pub mod region_pms_constrain_2;
#[doc = "REGION_PMS_CONSTRAIN_3 (rw) register accessor: SENSITIVE_REGION_PMS_CONSTRAIN_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_3::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_3::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@region_pms_constrain_3`] module"]
pub type REGION_PMS_CONSTRAIN_3 = crate::Reg<region_pms_constrain_3::REGION_PMS_CONSTRAIN_3_SPEC>;
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_3_REG"]
pub mod region_pms_constrain_3;
#[doc = "REGION_PMS_CONSTRAIN_4 (rw) register accessor: SENSITIVE_REGION_PMS_CONSTRAIN_4_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_4::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_4::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@region_pms_constrain_4`] module"]
pub type REGION_PMS_CONSTRAIN_4 = crate::Reg<region_pms_constrain_4::REGION_PMS_CONSTRAIN_4_SPEC>;
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_4_REG"]
pub mod region_pms_constrain_4;
#[doc = "REGION_PMS_CONSTRAIN_5 (rw) register accessor: SENSITIVE_REGION_PMS_CONSTRAIN_5_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_5::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_5::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@region_pms_constrain_5`] module"]
pub type REGION_PMS_CONSTRAIN_5 = crate::Reg<region_pms_constrain_5::REGION_PMS_CONSTRAIN_5_SPEC>;
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_5_REG"]
pub mod region_pms_constrain_5;
#[doc = "REGION_PMS_CONSTRAIN_6 (rw) register accessor: SENSITIVE_REGION_PMS_CONSTRAIN_6_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_6::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_6::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@region_pms_constrain_6`] module"]
pub type REGION_PMS_CONSTRAIN_6 = crate::Reg<region_pms_constrain_6::REGION_PMS_CONSTRAIN_6_SPEC>;
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_6_REG"]
pub mod region_pms_constrain_6;
#[doc = "REGION_PMS_CONSTRAIN_7 (rw) register accessor: SENSITIVE_REGION_PMS_CONSTRAIN_7_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_7::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_7::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@region_pms_constrain_7`] module"]
pub type REGION_PMS_CONSTRAIN_7 = crate::Reg<region_pms_constrain_7::REGION_PMS_CONSTRAIN_7_SPEC>;
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_7_REG"]
pub mod region_pms_constrain_7;
#[doc = "REGION_PMS_CONSTRAIN_8 (rw) register accessor: SENSITIVE_REGION_PMS_CONSTRAIN_8_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_8::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_8::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@region_pms_constrain_8`] module"]
pub type REGION_PMS_CONSTRAIN_8 = crate::Reg<region_pms_constrain_8::REGION_PMS_CONSTRAIN_8_SPEC>;
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_8_REG"]
pub mod region_pms_constrain_8;
#[doc = "REGION_PMS_CONSTRAIN_9 (rw) register accessor: SENSITIVE_REGION_PMS_CONSTRAIN_9_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_9::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_9::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@region_pms_constrain_9`] module"]
pub type REGION_PMS_CONSTRAIN_9 = crate::Reg<region_pms_constrain_9::REGION_PMS_CONSTRAIN_9_SPEC>;
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_9_REG"]
pub mod region_pms_constrain_9;
#[doc = "REGION_PMS_CONSTRAIN_10 (rw) register accessor: SENSITIVE_REGION_PMS_CONSTRAIN_10_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`region_pms_constrain_10::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_pms_constrain_10::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@region_pms_constrain_10`] module"]
pub type REGION_PMS_CONSTRAIN_10 =
    crate::Reg<region_pms_constrain_10::REGION_PMS_CONSTRAIN_10_SPEC>;
#[doc = "SENSITIVE_REGION_PMS_CONSTRAIN_10_REG"]
pub mod region_pms_constrain_10;
#[doc = "CORE_0_PIF_PMS_MONITOR_0 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_MONITOR_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_monitor_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_monitor_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_monitor_0`] module"]
pub type CORE_0_PIF_PMS_MONITOR_0 =
    crate::Reg<core_0_pif_pms_monitor_0::CORE_0_PIF_PMS_MONITOR_0_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_MONITOR_0_REG"]
pub mod core_0_pif_pms_monitor_0;
#[doc = "CORE_0_PIF_PMS_MONITOR_1 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_MONITOR_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_monitor_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_monitor_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_monitor_1`] module"]
pub type CORE_0_PIF_PMS_MONITOR_1 =
    crate::Reg<core_0_pif_pms_monitor_1::CORE_0_PIF_PMS_MONITOR_1_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_MONITOR_1_REG"]
pub mod core_0_pif_pms_monitor_1;
#[doc = "CORE_0_PIF_PMS_MONITOR_2 (r) register accessor: SENSITIVE_CORE_0_PIF_PMS_MONITOR_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_monitor_2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_monitor_2`] module"]
pub type CORE_0_PIF_PMS_MONITOR_2 =
    crate::Reg<core_0_pif_pms_monitor_2::CORE_0_PIF_PMS_MONITOR_2_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_MONITOR_2_REG"]
pub mod core_0_pif_pms_monitor_2;
#[doc = "CORE_0_PIF_PMS_MONITOR_3 (r) register accessor: SENSITIVE_CORE_0_PIF_PMS_MONITOR_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_monitor_3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_monitor_3`] module"]
pub type CORE_0_PIF_PMS_MONITOR_3 =
    crate::Reg<core_0_pif_pms_monitor_3::CORE_0_PIF_PMS_MONITOR_3_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_MONITOR_3_REG"]
pub mod core_0_pif_pms_monitor_3;
#[doc = "CORE_0_PIF_PMS_MONITOR_4 (rw) register accessor: SENSITIVE_CORE_0_PIF_PMS_MONITOR_4_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_monitor_4::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_monitor_4::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_monitor_4`] module"]
pub type CORE_0_PIF_PMS_MONITOR_4 =
    crate::Reg<core_0_pif_pms_monitor_4::CORE_0_PIF_PMS_MONITOR_4_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_MONITOR_4_REG"]
pub mod core_0_pif_pms_monitor_4;
#[doc = "CORE_0_PIF_PMS_MONITOR_5 (r) register accessor: SENSITIVE_CORE_0_PIF_PMS_MONITOR_5_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_monitor_5::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_monitor_5`] module"]
pub type CORE_0_PIF_PMS_MONITOR_5 =
    crate::Reg<core_0_pif_pms_monitor_5::CORE_0_PIF_PMS_MONITOR_5_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_MONITOR_5_REG"]
pub mod core_0_pif_pms_monitor_5;
#[doc = "CORE_0_PIF_PMS_MONITOR_6 (r) register accessor: SENSITIVE_CORE_0_PIF_PMS_MONITOR_6_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_monitor_6::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_0_pif_pms_monitor_6`] module"]
pub type CORE_0_PIF_PMS_MONITOR_6 =
    crate::Reg<core_0_pif_pms_monitor_6::CORE_0_PIF_PMS_MONITOR_6_SPEC>;
#[doc = "SENSITIVE_CORE_0_PIF_PMS_MONITOR_6_REG"]
pub mod core_0_pif_pms_monitor_6;
#[doc = "BACKUP_BUS_PMS_CONSTRAIN_0 (rw) register accessor: SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_constrain_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`backup_bus_pms_constrain_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@backup_bus_pms_constrain_0`] module"]
pub type BACKUP_BUS_PMS_CONSTRAIN_0 =
    crate::Reg<backup_bus_pms_constrain_0::BACKUP_BUS_PMS_CONSTRAIN_0_SPEC>;
#[doc = "SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_0_REG"]
pub mod backup_bus_pms_constrain_0;
#[doc = "BACKUP_BUS_PMS_CONSTRAIN_1 (rw) register accessor: SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_constrain_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`backup_bus_pms_constrain_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@backup_bus_pms_constrain_1`] module"]
pub type BACKUP_BUS_PMS_CONSTRAIN_1 =
    crate::Reg<backup_bus_pms_constrain_1::BACKUP_BUS_PMS_CONSTRAIN_1_SPEC>;
#[doc = "SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_1_REG"]
pub mod backup_bus_pms_constrain_1;
#[doc = "BACKUP_BUS_PMS_CONSTRAIN_2 (rw) register accessor: SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_constrain_2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`backup_bus_pms_constrain_2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@backup_bus_pms_constrain_2`] module"]
pub type BACKUP_BUS_PMS_CONSTRAIN_2 =
    crate::Reg<backup_bus_pms_constrain_2::BACKUP_BUS_PMS_CONSTRAIN_2_SPEC>;
#[doc = "SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_2_REG"]
pub mod backup_bus_pms_constrain_2;
#[doc = "BACKUP_BUS_PMS_CONSTRAIN_3 (rw) register accessor: SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_constrain_3::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`backup_bus_pms_constrain_3::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@backup_bus_pms_constrain_3`] module"]
pub type BACKUP_BUS_PMS_CONSTRAIN_3 =
    crate::Reg<backup_bus_pms_constrain_3::BACKUP_BUS_PMS_CONSTRAIN_3_SPEC>;
#[doc = "SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_3_REG"]
pub mod backup_bus_pms_constrain_3;
#[doc = "BACKUP_BUS_PMS_CONSTRAIN_4 (rw) register accessor: SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_4_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_constrain_4::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`backup_bus_pms_constrain_4::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@backup_bus_pms_constrain_4`] module"]
pub type BACKUP_BUS_PMS_CONSTRAIN_4 =
    crate::Reg<backup_bus_pms_constrain_4::BACKUP_BUS_PMS_CONSTRAIN_4_SPEC>;
#[doc = "SENSITIVE_BACKUP_BUS_PMS_CONSTRAIN_4_REG"]
pub mod backup_bus_pms_constrain_4;
#[doc = "BACKUP_BUS_PMS_MONITOR_0 (rw) register accessor: SENSITIVE_BACKUP_BUS_PMS_MONITOR_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_monitor_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`backup_bus_pms_monitor_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@backup_bus_pms_monitor_0`] module"]
pub type BACKUP_BUS_PMS_MONITOR_0 =
    crate::Reg<backup_bus_pms_monitor_0::BACKUP_BUS_PMS_MONITOR_0_SPEC>;
#[doc = "SENSITIVE_BACKUP_BUS_PMS_MONITOR_0_REG"]
pub mod backup_bus_pms_monitor_0;
#[doc = "BACKUP_BUS_PMS_MONITOR_1 (rw) register accessor: SENSITIVE_BACKUP_BUS_PMS_MONITOR_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_monitor_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`backup_bus_pms_monitor_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@backup_bus_pms_monitor_1`] module"]
pub type BACKUP_BUS_PMS_MONITOR_1 =
    crate::Reg<backup_bus_pms_monitor_1::BACKUP_BUS_PMS_MONITOR_1_SPEC>;
#[doc = "SENSITIVE_BACKUP_BUS_PMS_MONITOR_1_REG"]
pub mod backup_bus_pms_monitor_1;
#[doc = "BACKUP_BUS_PMS_MONITOR_2 (r) register accessor: SENSITIVE_BACKUP_BUS_PMS_MONITOR_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_monitor_2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@backup_bus_pms_monitor_2`] module"]
pub type BACKUP_BUS_PMS_MONITOR_2 =
    crate::Reg<backup_bus_pms_monitor_2::BACKUP_BUS_PMS_MONITOR_2_SPEC>;
#[doc = "SENSITIVE_BACKUP_BUS_PMS_MONITOR_2_REG"]
pub mod backup_bus_pms_monitor_2;
#[doc = "BACKUP_BUS_PMS_MONITOR_3 (r) register accessor: SENSITIVE_BACKUP_BUS_PMS_MONITOR_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`backup_bus_pms_monitor_3::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@backup_bus_pms_monitor_3`] module"]
pub type BACKUP_BUS_PMS_MONITOR_3 =
    crate::Reg<backup_bus_pms_monitor_3::BACKUP_BUS_PMS_MONITOR_3_SPEC>;
#[doc = "SENSITIVE_BACKUP_BUS_PMS_MONITOR_3_REG"]
pub mod backup_bus_pms_monitor_3;
#[doc = "CLOCK_GATE (rw) register accessor: SENSITIVE_CLOCK_GATE_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`clock_gate::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clock_gate::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clock_gate`] module"]
pub type CLOCK_GATE = crate::Reg<clock_gate::CLOCK_GATE_SPEC>;
#[doc = "SENSITIVE_CLOCK_GATE_REG"]
pub mod clock_gate;
pub use crate::aes::{date, DATE};
