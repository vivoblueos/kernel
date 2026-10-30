#[doc = "Register `SPI_SMEM_AC` reader"]
pub type R = crate::R<SPI_SMEM_AC_SPEC>;
#[doc = "Field `SPI_SMEM_CS_SETUP` reader - For SPI0 and SPI1, spi cs is enable when spi is in prepare phase. 1: enable 0: disable."]
pub type SPI_SMEM_CS_SETUP_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_CS_HOLD` reader - For SPI0 and SPI1, spi cs keep low when spi is in done phase. 1: enable 0: disable."]
pub type SPI_SMEM_CS_HOLD_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_CS_SETUP_TIME` reader - For spi0, (cycles-1) of prepare phase by spi clock this bits are combined with spi_mem_cs_setup bit."]
pub type SPI_SMEM_CS_SETUP_TIME_R = crate::FieldReader;
#[doc = "Field `SPI_SMEM_CS_HOLD_TIME` reader - For SPI0 and SPI1, spi cs signal is delayed to inactive by spi clock this bits are combined with spi_mem_cs_hold bit."]
pub type SPI_SMEM_CS_HOLD_TIME_R = crate::FieldReader;
#[doc = "Field `SPI_SMEM_ECC_CS_HOLD_TIME` reader - SPI_SMEM_CS_HOLD_TIME + SPI_SMEM_ECC_CS_HOLD_TIME is the SPI0 and SPI1 CS hold cycles in ECC mode when accessed external RAM."]
pub type SPI_SMEM_ECC_CS_HOLD_TIME_R = crate::FieldReader;
#[doc = "Field `SPI_SMEM_ECC_SKIP_PAGE_CORNER` reader - 1: SPI0 skips page corner when accesses external RAM. 0: Not skip page corner when accesses external RAM."]
pub type SPI_SMEM_ECC_SKIP_PAGE_CORNER_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_ECC_16TO18_BYTE_EN` reader - Set this bit to enable SPI0 and SPI1 ECC 16 bytes data with 2 ECC bytes mode when accesses external RAM."]
pub type SPI_SMEM_ECC_16TO18_BYTE_EN_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_CS_HOLD_DELAY` reader - These bits are used to set the minimum CS high time tSHSL between SPI burst transfer when accesses to external RAM. tSHSL is (SPI_SMEM_CS_HOLD_DELAY\\[5:0\\] + 1) MSPI core clock cycles."]
pub type SPI_SMEM_CS_HOLD_DELAY_R = crate::FieldReader;
#[doc = "Field `SPI_SMEM_SPLIT_TRANS_EN` reader - Set this bit to enable SPI0 split one AXI accesses EXT_RAM transfer into two SPI transfers when one transfer will cross flash/EXT_RAM page corner, valid no matter whether there is an ECC region or not."]
pub type SPI_SMEM_SPLIT_TRANS_EN_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - For SPI0 and SPI1, spi cs is enable when spi is in prepare phase. 1: enable 0: disable."]
    #[inline(always)]
    pub fn spi_smem_cs_setup(&self) -> SPI_SMEM_CS_SETUP_R {
        SPI_SMEM_CS_SETUP_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - For SPI0 and SPI1, spi cs keep low when spi is in done phase. 1: enable 0: disable."]
    #[inline(always)]
    pub fn spi_smem_cs_hold(&self) -> SPI_SMEM_CS_HOLD_R {
        SPI_SMEM_CS_HOLD_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:6 - For spi0, (cycles-1) of prepare phase by spi clock this bits are combined with spi_mem_cs_setup bit."]
    #[inline(always)]
    pub fn spi_smem_cs_setup_time(&self) -> SPI_SMEM_CS_SETUP_TIME_R {
        SPI_SMEM_CS_SETUP_TIME_R::new(((self.bits >> 2) & 0x1f) as u8)
    }
    #[doc = "Bits 7:11 - For SPI0 and SPI1, spi cs signal is delayed to inactive by spi clock this bits are combined with spi_mem_cs_hold bit."]
    #[inline(always)]
    pub fn spi_smem_cs_hold_time(&self) -> SPI_SMEM_CS_HOLD_TIME_R {
        SPI_SMEM_CS_HOLD_TIME_R::new(((self.bits >> 7) & 0x1f) as u8)
    }
    #[doc = "Bits 12:14 - SPI_SMEM_CS_HOLD_TIME + SPI_SMEM_ECC_CS_HOLD_TIME is the SPI0 and SPI1 CS hold cycles in ECC mode when accessed external RAM."]
    #[inline(always)]
    pub fn spi_smem_ecc_cs_hold_time(&self) -> SPI_SMEM_ECC_CS_HOLD_TIME_R {
        SPI_SMEM_ECC_CS_HOLD_TIME_R::new(((self.bits >> 12) & 7) as u8)
    }
    #[doc = "Bit 15 - 1: SPI0 skips page corner when accesses external RAM. 0: Not skip page corner when accesses external RAM."]
    #[inline(always)]
    pub fn spi_smem_ecc_skip_page_corner(&self) -> SPI_SMEM_ECC_SKIP_PAGE_CORNER_R {
        SPI_SMEM_ECC_SKIP_PAGE_CORNER_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Set this bit to enable SPI0 and SPI1 ECC 16 bytes data with 2 ECC bytes mode when accesses external RAM."]
    #[inline(always)]
    pub fn spi_smem_ecc_16to18_byte_en(&self) -> SPI_SMEM_ECC_16TO18_BYTE_EN_R {
        SPI_SMEM_ECC_16TO18_BYTE_EN_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bits 25:30 - These bits are used to set the minimum CS high time tSHSL between SPI burst transfer when accesses to external RAM. tSHSL is (SPI_SMEM_CS_HOLD_DELAY\\[5:0\\] + 1) MSPI core clock cycles."]
    #[inline(always)]
    pub fn spi_smem_cs_hold_delay(&self) -> SPI_SMEM_CS_HOLD_DELAY_R {
        SPI_SMEM_CS_HOLD_DELAY_R::new(((self.bits >> 25) & 0x3f) as u8)
    }
    #[doc = "Bit 31 - Set this bit to enable SPI0 split one AXI accesses EXT_RAM transfer into two SPI transfers when one transfer will cross flash/EXT_RAM page corner, valid no matter whether there is an ECC region or not."]
    #[inline(always)]
    pub fn spi_smem_split_trans_en(&self) -> SPI_SMEM_SPLIT_TRANS_EN_R {
        SPI_SMEM_SPLIT_TRANS_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SPI_SMEM_AC")
            .field("spi_smem_cs_setup", &self.spi_smem_cs_setup())
            .field("spi_smem_cs_hold", &self.spi_smem_cs_hold())
            .field("spi_smem_cs_setup_time", &self.spi_smem_cs_setup_time())
            .field("spi_smem_cs_hold_time", &self.spi_smem_cs_hold_time())
            .field(
                "spi_smem_ecc_cs_hold_time",
                &self.spi_smem_ecc_cs_hold_time(),
            )
            .field(
                "spi_smem_ecc_skip_page_corner",
                &self.spi_smem_ecc_skip_page_corner(),
            )
            .field(
                "spi_smem_ecc_16to18_byte_en",
                &self.spi_smem_ecc_16to18_byte_en(),
            )
            .field("spi_smem_cs_hold_delay", &self.spi_smem_cs_hold_delay())
            .field("spi_smem_split_trans_en", &self.spi_smem_split_trans_en())
            .finish()
    }
}
#[doc = "MSPI external RAM ECC and SPI CS timing control register\n\nYou can [`read`](crate::Reg::read) this register and get [`spi_smem_ac::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SPI_SMEM_AC_SPEC;
impl crate::RegisterSpec for SPI_SMEM_AC_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`spi_smem_ac::R`](R) reader structure"]
impl crate::Readable for SPI_SMEM_AC_SPEC {}
#[doc = "`reset()` method sets SPI_SMEM_AC to value 0x8000_b084"]
impl crate::Resettable for SPI_SMEM_AC_SPEC {
    const RESET_VALUE: u32 = 0x8000_b084;
}
