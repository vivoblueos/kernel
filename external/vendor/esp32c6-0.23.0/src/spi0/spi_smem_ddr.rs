#[doc = "Register `SPI_SMEM_DDR` reader"]
pub type R = crate::R<SPI_SMEM_DDR_SPEC>;
#[doc = "Field `EN` reader - 1: in DDR mode, 0 in SDR mode"]
pub type EN_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_VAR_DUMMY` reader - Set the bit to enable variable dummy cycle in spi DDR mode."]
pub type SPI_SMEM_VAR_DUMMY_R = crate::BitReader;
#[doc = "Field `RDAT_SWP` reader - Set the bit to reorder rx data of the word in spi DDR mode."]
pub type RDAT_SWP_R = crate::BitReader;
#[doc = "Field `WDAT_SWP` reader - Set the bit to reorder tx data of the word in spi DDR mode."]
pub type WDAT_SWP_R = crate::BitReader;
#[doc = "Field `CMD_DIS` reader - the bit is used to disable dual edge in command phase when DDR mode."]
pub type CMD_DIS_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_OUTMINBYTELEN` reader - It is the minimum output data length in the DDR psram."]
pub type SPI_SMEM_OUTMINBYTELEN_R = crate::FieldReader;
#[doc = "Field `SPI_SMEM_TX_DDR_MSK_EN` reader - Set this bit to mask the first or the last byte in SPI0 ECC DDR write mode, when accesses to external RAM."]
pub type SPI_SMEM_TX_DDR_MSK_EN_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_RX_DDR_MSK_EN` reader - Set this bit to mask the first or the last byte in SPI0 ECC DDR read mode, when accesses to external RAM."]
pub type SPI_SMEM_RX_DDR_MSK_EN_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_USR_DDR_DQS_THD` reader - The delay number of data strobe which from memory based on SPI clock."]
pub type SPI_SMEM_USR_DDR_DQS_THD_R = crate::FieldReader;
#[doc = "Field `DQS_LOOP` reader - 1: Do not need the input of SPI_DQS signal, SPI0 starts to receive data when spi0_slv_st is in SPI_MEM_DIN state. It is used when there is no SPI_DQS signal or SPI_DQS signal is not stable. 0: SPI0 starts to store data at the positive and negative edge of SPI_DQS."]
pub type DQS_LOOP_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_CLK_DIFF_EN` reader - Set this bit to enable the differential SPI_CLK#."]
pub type SPI_SMEM_CLK_DIFF_EN_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_DQS_CA_IN` reader - Set this bit to enable the input of SPI_DQS signal in SPI phases of CMD and ADDR."]
pub type SPI_SMEM_DQS_CA_IN_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_HYPERBUS_DUMMY_2X` reader - Set this bit to enable the vary dummy function in SPI HyperBus mode, when SPI0 accesses flash or SPI1 accesses flash or sram."]
pub type SPI_SMEM_HYPERBUS_DUMMY_2X_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_CLK_DIFF_INV` reader - Set this bit to invert SPI_DIFF when accesses to external RAM. ."]
pub type SPI_SMEM_CLK_DIFF_INV_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_OCTA_RAM_ADDR` reader - Set this bit to enable octa_ram address out when accesses to external RAM, which means ADDR_OUT\\[31:0\\] = {spi_usr_addr_value\\[25:4\\], 6'd0, spi_usr_addr_value\\[3:1\\], 1'b0}."]
pub type SPI_SMEM_OCTA_RAM_ADDR_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_HYPERBUS_CA` reader - Set this bit to enable HyperRAM address out when accesses to external RAM, which means ADDR_OUT\\[31:0\\] = {spi_usr_addr_value\\[19:4\\], 13'd0, spi_usr_addr_value\\[3:1\\]}."]
pub type SPI_SMEM_HYPERBUS_CA_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - 1: in DDR mode, 0 in SDR mode"]
    #[inline(always)]
    pub fn en(&self) -> EN_R {
        EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set the bit to enable variable dummy cycle in spi DDR mode."]
    #[inline(always)]
    pub fn spi_smem_var_dummy(&self) -> SPI_SMEM_VAR_DUMMY_R {
        SPI_SMEM_VAR_DUMMY_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set the bit to reorder rx data of the word in spi DDR mode."]
    #[inline(always)]
    pub fn rdat_swp(&self) -> RDAT_SWP_R {
        RDAT_SWP_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Set the bit to reorder tx data of the word in spi DDR mode."]
    #[inline(always)]
    pub fn wdat_swp(&self) -> WDAT_SWP_R {
        WDAT_SWP_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - the bit is used to disable dual edge in command phase when DDR mode."]
    #[inline(always)]
    pub fn cmd_dis(&self) -> CMD_DIS_R {
        CMD_DIS_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bits 5:11 - It is the minimum output data length in the DDR psram."]
    #[inline(always)]
    pub fn spi_smem_outminbytelen(&self) -> SPI_SMEM_OUTMINBYTELEN_R {
        SPI_SMEM_OUTMINBYTELEN_R::new(((self.bits >> 5) & 0x7f) as u8)
    }
    #[doc = "Bit 12 - Set this bit to mask the first or the last byte in SPI0 ECC DDR write mode, when accesses to external RAM."]
    #[inline(always)]
    pub fn spi_smem_tx_ddr_msk_en(&self) -> SPI_SMEM_TX_DDR_MSK_EN_R {
        SPI_SMEM_TX_DDR_MSK_EN_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Set this bit to mask the first or the last byte in SPI0 ECC DDR read mode, when accesses to external RAM."]
    #[inline(always)]
    pub fn spi_smem_rx_ddr_msk_en(&self) -> SPI_SMEM_RX_DDR_MSK_EN_R {
        SPI_SMEM_RX_DDR_MSK_EN_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bits 14:20 - The delay number of data strobe which from memory based on SPI clock."]
    #[inline(always)]
    pub fn spi_smem_usr_ddr_dqs_thd(&self) -> SPI_SMEM_USR_DDR_DQS_THD_R {
        SPI_SMEM_USR_DDR_DQS_THD_R::new(((self.bits >> 14) & 0x7f) as u8)
    }
    #[doc = "Bit 21 - 1: Do not need the input of SPI_DQS signal, SPI0 starts to receive data when spi0_slv_st is in SPI_MEM_DIN state. It is used when there is no SPI_DQS signal or SPI_DQS signal is not stable. 0: SPI0 starts to store data at the positive and negative edge of SPI_DQS."]
    #[inline(always)]
    pub fn dqs_loop(&self) -> DQS_LOOP_R {
        DQS_LOOP_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 24 - Set this bit to enable the differential SPI_CLK#."]
    #[inline(always)]
    pub fn spi_smem_clk_diff_en(&self) -> SPI_SMEM_CLK_DIFF_EN_R {
        SPI_SMEM_CLK_DIFF_EN_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 26 - Set this bit to enable the input of SPI_DQS signal in SPI phases of CMD and ADDR."]
    #[inline(always)]
    pub fn spi_smem_dqs_ca_in(&self) -> SPI_SMEM_DQS_CA_IN_R {
        SPI_SMEM_DQS_CA_IN_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - Set this bit to enable the vary dummy function in SPI HyperBus mode, when SPI0 accesses flash or SPI1 accesses flash or sram."]
    #[inline(always)]
    pub fn spi_smem_hyperbus_dummy_2x(&self) -> SPI_SMEM_HYPERBUS_DUMMY_2X_R {
        SPI_SMEM_HYPERBUS_DUMMY_2X_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - Set this bit to invert SPI_DIFF when accesses to external RAM. ."]
    #[inline(always)]
    pub fn spi_smem_clk_diff_inv(&self) -> SPI_SMEM_CLK_DIFF_INV_R {
        SPI_SMEM_CLK_DIFF_INV_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - Set this bit to enable octa_ram address out when accesses to external RAM, which means ADDR_OUT\\[31:0\\] = {spi_usr_addr_value\\[25:4\\], 6'd0, spi_usr_addr_value\\[3:1\\], 1'b0}."]
    #[inline(always)]
    pub fn spi_smem_octa_ram_addr(&self) -> SPI_SMEM_OCTA_RAM_ADDR_R {
        SPI_SMEM_OCTA_RAM_ADDR_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - Set this bit to enable HyperRAM address out when accesses to external RAM, which means ADDR_OUT\\[31:0\\] = {spi_usr_addr_value\\[19:4\\], 13'd0, spi_usr_addr_value\\[3:1\\]}."]
    #[inline(always)]
    pub fn spi_smem_hyperbus_ca(&self) -> SPI_SMEM_HYPERBUS_CA_R {
        SPI_SMEM_HYPERBUS_CA_R::new(((self.bits >> 30) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SPI_SMEM_DDR")
            .field("en", &self.en())
            .field("spi_smem_var_dummy", &self.spi_smem_var_dummy())
            .field("rdat_swp", &self.rdat_swp())
            .field("wdat_swp", &self.wdat_swp())
            .field("cmd_dis", &self.cmd_dis())
            .field("spi_smem_outminbytelen", &self.spi_smem_outminbytelen())
            .field("spi_smem_tx_ddr_msk_en", &self.spi_smem_tx_ddr_msk_en())
            .field("spi_smem_rx_ddr_msk_en", &self.spi_smem_rx_ddr_msk_en())
            .field("spi_smem_usr_ddr_dqs_thd", &self.spi_smem_usr_ddr_dqs_thd())
            .field("dqs_loop", &self.dqs_loop())
            .field("spi_smem_clk_diff_en", &self.spi_smem_clk_diff_en())
            .field("spi_smem_dqs_ca_in", &self.spi_smem_dqs_ca_in())
            .field(
                "spi_smem_hyperbus_dummy_2x",
                &self.spi_smem_hyperbus_dummy_2x(),
            )
            .field("spi_smem_clk_diff_inv", &self.spi_smem_clk_diff_inv())
            .field("spi_smem_octa_ram_addr", &self.spi_smem_octa_ram_addr())
            .field("spi_smem_hyperbus_ca", &self.spi_smem_hyperbus_ca())
            .finish()
    }
}
#[doc = "SPI0 external RAM DDR mode control register\n\nYou can [`read`](crate::Reg::read) this register and get [`spi_smem_ddr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SPI_SMEM_DDR_SPEC;
impl crate::RegisterSpec for SPI_SMEM_DDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`spi_smem_ddr::R`](R) reader structure"]
impl crate::Readable for SPI_SMEM_DDR_SPEC {}
#[doc = "`reset()` method sets SPI_SMEM_DDR to value 0x3020"]
impl crate::Resettable for SPI_SMEM_DDR_SPEC {
    const RESET_VALUE: u32 = 0x3020;
}
