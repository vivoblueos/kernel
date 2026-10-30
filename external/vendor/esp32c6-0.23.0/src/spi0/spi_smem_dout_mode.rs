#[doc = "Register `SPI_SMEM_DOUT_MODE` reader"]
pub type R = crate::R<SPI_SMEM_DOUT_MODE_SPEC>;
#[doc = "Field `SPI_SMEM_DOUT0_MODE` reader - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
pub type SPI_SMEM_DOUT0_MODE_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_DOUT1_MODE` reader - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
pub type SPI_SMEM_DOUT1_MODE_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_DOUT2_MODE` reader - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
pub type SPI_SMEM_DOUT2_MODE_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_DOUT3_MODE` reader - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
pub type SPI_SMEM_DOUT3_MODE_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_DOUT4_MODE` reader - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
pub type SPI_SMEM_DOUT4_MODE_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_DOUT5_MODE` reader - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
pub type SPI_SMEM_DOUT5_MODE_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_DOUT6_MODE` reader - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
pub type SPI_SMEM_DOUT6_MODE_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_DOUT7_MODE` reader - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
pub type SPI_SMEM_DOUT7_MODE_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_DOUTS_MODE` reader - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
pub type SPI_SMEM_DOUTS_MODE_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
    #[inline(always)]
    pub fn spi_smem_dout0_mode(&self) -> SPI_SMEM_DOUT0_MODE_R {
        SPI_SMEM_DOUT0_MODE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
    #[inline(always)]
    pub fn spi_smem_dout1_mode(&self) -> SPI_SMEM_DOUT1_MODE_R {
        SPI_SMEM_DOUT1_MODE_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
    #[inline(always)]
    pub fn spi_smem_dout2_mode(&self) -> SPI_SMEM_DOUT2_MODE_R {
        SPI_SMEM_DOUT2_MODE_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
    #[inline(always)]
    pub fn spi_smem_dout3_mode(&self) -> SPI_SMEM_DOUT3_MODE_R {
        SPI_SMEM_DOUT3_MODE_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
    #[inline(always)]
    pub fn spi_smem_dout4_mode(&self) -> SPI_SMEM_DOUT4_MODE_R {
        SPI_SMEM_DOUT4_MODE_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
    #[inline(always)]
    pub fn spi_smem_dout5_mode(&self) -> SPI_SMEM_DOUT5_MODE_R {
        SPI_SMEM_DOUT5_MODE_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
    #[inline(always)]
    pub fn spi_smem_dout6_mode(&self) -> SPI_SMEM_DOUT6_MODE_R {
        SPI_SMEM_DOUT6_MODE_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
    #[inline(always)]
    pub fn spi_smem_dout7_mode(&self) -> SPI_SMEM_DOUT7_MODE_R {
        SPI_SMEM_DOUT7_MODE_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - the output signals are delayed by system clock cycles, 0: output without delayed, 1: output with the posedge of clk_apb,2 output with the negedge of clk_apb, 3: output with the posedge of clk_160,4 output with the negedge of clk_160,5: output with the spi_clk high edge ,6: output with the spi_clk low edge"]
    #[inline(always)]
    pub fn spi_smem_douts_mode(&self) -> SPI_SMEM_DOUTS_MODE_R {
        SPI_SMEM_DOUTS_MODE_R::new(((self.bits >> 8) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SPI_SMEM_DOUT_MODE")
            .field("spi_smem_dout0_mode", &self.spi_smem_dout0_mode())
            .field("spi_smem_dout1_mode", &self.spi_smem_dout1_mode())
            .field("spi_smem_dout2_mode", &self.spi_smem_dout2_mode())
            .field("spi_smem_dout3_mode", &self.spi_smem_dout3_mode())
            .field("spi_smem_dout4_mode", &self.spi_smem_dout4_mode())
            .field("spi_smem_dout5_mode", &self.spi_smem_dout5_mode())
            .field("spi_smem_dout6_mode", &self.spi_smem_dout6_mode())
            .field("spi_smem_dout7_mode", &self.spi_smem_dout7_mode())
            .field("spi_smem_douts_mode", &self.spi_smem_douts_mode())
            .finish()
    }
}
#[doc = "MSPI external RAM output timing adjustment control register\n\nYou can [`read`](crate::Reg::read) this register and get [`spi_smem_dout_mode::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SPI_SMEM_DOUT_MODE_SPEC;
impl crate::RegisterSpec for SPI_SMEM_DOUT_MODE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`spi_smem_dout_mode::R`](R) reader structure"]
impl crate::Readable for SPI_SMEM_DOUT_MODE_SPEC {}
#[doc = "`reset()` method sets SPI_SMEM_DOUT_MODE to value 0"]
impl crate::Resettable for SPI_SMEM_DOUT_MODE_SPEC {}
