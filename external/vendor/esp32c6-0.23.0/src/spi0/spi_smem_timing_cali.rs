#[doc = "Register `SPI_SMEM_TIMING_CALI` reader"]
pub type R = crate::R<SPI_SMEM_TIMING_CALI_SPEC>;
#[doc = "Field `SPI_SMEM_TIMING_CLK_ENA` reader - For sram, the bit is used to enable timing adjust clock for all reading operations."]
pub type SPI_SMEM_TIMING_CLK_ENA_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_TIMING_CALI` reader - For sram, the bit is used to enable timing auto-calibration for all reading operations."]
pub type SPI_SMEM_TIMING_CALI_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_EXTRA_DUMMY_CYCLELEN` reader - For sram, add extra dummy spi clock cycle length for spi clock calibration."]
pub type SPI_SMEM_EXTRA_DUMMY_CYCLELEN_R = crate::FieldReader;
#[doc = "Field `SPI_SMEM_DLL_TIMING_CALI` reader - Set this bit to enable DLL for timing calibration in DDR mode when accessed to EXT_RAM."]
pub type SPI_SMEM_DLL_TIMING_CALI_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - For sram, the bit is used to enable timing adjust clock for all reading operations."]
    #[inline(always)]
    pub fn spi_smem_timing_clk_ena(&self) -> SPI_SMEM_TIMING_CLK_ENA_R {
        SPI_SMEM_TIMING_CLK_ENA_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - For sram, the bit is used to enable timing auto-calibration for all reading operations."]
    #[inline(always)]
    pub fn spi_smem_timing_cali(&self) -> SPI_SMEM_TIMING_CALI_R {
        SPI_SMEM_TIMING_CALI_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:4 - For sram, add extra dummy spi clock cycle length for spi clock calibration."]
    #[inline(always)]
    pub fn spi_smem_extra_dummy_cyclelen(&self) -> SPI_SMEM_EXTRA_DUMMY_CYCLELEN_R {
        SPI_SMEM_EXTRA_DUMMY_CYCLELEN_R::new(((self.bits >> 2) & 7) as u8)
    }
    #[doc = "Bit 5 - Set this bit to enable DLL for timing calibration in DDR mode when accessed to EXT_RAM."]
    #[inline(always)]
    pub fn spi_smem_dll_timing_cali(&self) -> SPI_SMEM_DLL_TIMING_CALI_R {
        SPI_SMEM_DLL_TIMING_CALI_R::new(((self.bits >> 5) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SPI_SMEM_TIMING_CALI")
            .field("spi_smem_timing_clk_ena", &self.spi_smem_timing_clk_ena())
            .field("spi_smem_timing_cali", &self.spi_smem_timing_cali())
            .field(
                "spi_smem_extra_dummy_cyclelen",
                &self.spi_smem_extra_dummy_cyclelen(),
            )
            .field("spi_smem_dll_timing_cali", &self.spi_smem_dll_timing_cali())
            .finish()
    }
}
#[doc = "MSPI external RAM timing calibration register\n\nYou can [`read`](crate::Reg::read) this register and get [`spi_smem_timing_cali::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SPI_SMEM_TIMING_CALI_SPEC;
impl crate::RegisterSpec for SPI_SMEM_TIMING_CALI_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`spi_smem_timing_cali::R`](R) reader structure"]
impl crate::Readable for SPI_SMEM_TIMING_CALI_SPEC {}
#[doc = "`reset()` method sets SPI_SMEM_TIMING_CALI to value 0x01"]
impl crate::Resettable for SPI_SMEM_TIMING_CALI_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
