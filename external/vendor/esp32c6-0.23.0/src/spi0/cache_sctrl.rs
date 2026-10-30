#[doc = "Register `CACHE_SCTRL` reader"]
pub type R = crate::R<CACHE_SCTRL_SPEC>;
#[doc = "Field `CACHE_USR_SADDR_4BYTE` reader - For SPI0, In the external RAM mode, cache read flash with 4 bytes command, 1: enable, 0:disable."]
pub type CACHE_USR_SADDR_4BYTE_R = crate::BitReader;
#[doc = "Field `USR_SRAM_DIO` reader - For SPI0, In the external RAM mode, spi dual I/O mode enable, 1: enable, 0:disable"]
pub type USR_SRAM_DIO_R = crate::BitReader;
#[doc = "Field `USR_SRAM_QIO` reader - For SPI0, In the external RAM mode, spi quad I/O mode enable, 1: enable, 0:disable"]
pub type USR_SRAM_QIO_R = crate::BitReader;
#[doc = "Field `USR_WR_SRAM_DUMMY` reader - For SPI0, In the external RAM mode, it is the enable bit of dummy phase for write operations."]
pub type USR_WR_SRAM_DUMMY_R = crate::BitReader;
#[doc = "Field `USR_RD_SRAM_DUMMY` reader - For SPI0, In the external RAM mode, it is the enable bit of dummy phase for read operations."]
pub type USR_RD_SRAM_DUMMY_R = crate::BitReader;
#[doc = "Field `CACHE_SRAM_USR_RCMD` reader - For SPI0, In the external RAM mode cache read external RAM for user define command."]
pub type CACHE_SRAM_USR_RCMD_R = crate::BitReader;
#[doc = "Field `SRAM_RDUMMY_CYCLELEN` reader - For SPI0, In the external RAM mode, it is the length in bits of read dummy phase. The register value shall be (bit_num-1)."]
pub type SRAM_RDUMMY_CYCLELEN_R = crate::FieldReader;
#[doc = "Field `SRAM_ADDR_BITLEN` reader - For SPI0, In the external RAM mode, it is the length in bits of address phase. The register value shall be (bit_num-1)."]
pub type SRAM_ADDR_BITLEN_R = crate::FieldReader;
#[doc = "Field `CACHE_SRAM_USR_WCMD` reader - For SPI0, In the external RAM mode cache write sram for user define command"]
pub type CACHE_SRAM_USR_WCMD_R = crate::BitReader;
#[doc = "Field `SRAM_OCT` reader - reserved"]
pub type SRAM_OCT_R = crate::BitReader;
#[doc = "Field `SRAM_WDUMMY_CYCLELEN` reader - For SPI0, In the external RAM mode, it is the length in bits of write dummy phase. The register value shall be (bit_num-1)."]
pub type SRAM_WDUMMY_CYCLELEN_R = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - For SPI0, In the external RAM mode, cache read flash with 4 bytes command, 1: enable, 0:disable."]
    #[inline(always)]
    pub fn cache_usr_saddr_4byte(&self) -> CACHE_USR_SADDR_4BYTE_R {
        CACHE_USR_SADDR_4BYTE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - For SPI0, In the external RAM mode, spi dual I/O mode enable, 1: enable, 0:disable"]
    #[inline(always)]
    pub fn usr_sram_dio(&self) -> USR_SRAM_DIO_R {
        USR_SRAM_DIO_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - For SPI0, In the external RAM mode, spi quad I/O mode enable, 1: enable, 0:disable"]
    #[inline(always)]
    pub fn usr_sram_qio(&self) -> USR_SRAM_QIO_R {
        USR_SRAM_QIO_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - For SPI0, In the external RAM mode, it is the enable bit of dummy phase for write operations."]
    #[inline(always)]
    pub fn usr_wr_sram_dummy(&self) -> USR_WR_SRAM_DUMMY_R {
        USR_WR_SRAM_DUMMY_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - For SPI0, In the external RAM mode, it is the enable bit of dummy phase for read operations."]
    #[inline(always)]
    pub fn usr_rd_sram_dummy(&self) -> USR_RD_SRAM_DUMMY_R {
        USR_RD_SRAM_DUMMY_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - For SPI0, In the external RAM mode cache read external RAM for user define command."]
    #[inline(always)]
    pub fn cache_sram_usr_rcmd(&self) -> CACHE_SRAM_USR_RCMD_R {
        CACHE_SRAM_USR_RCMD_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bits 6:11 - For SPI0, In the external RAM mode, it is the length in bits of read dummy phase. The register value shall be (bit_num-1)."]
    #[inline(always)]
    pub fn sram_rdummy_cyclelen(&self) -> SRAM_RDUMMY_CYCLELEN_R {
        SRAM_RDUMMY_CYCLELEN_R::new(((self.bits >> 6) & 0x3f) as u8)
    }
    #[doc = "Bits 14:19 - For SPI0, In the external RAM mode, it is the length in bits of address phase. The register value shall be (bit_num-1)."]
    #[inline(always)]
    pub fn sram_addr_bitlen(&self) -> SRAM_ADDR_BITLEN_R {
        SRAM_ADDR_BITLEN_R::new(((self.bits >> 14) & 0x3f) as u8)
    }
    #[doc = "Bit 20 - For SPI0, In the external RAM mode cache write sram for user define command"]
    #[inline(always)]
    pub fn cache_sram_usr_wcmd(&self) -> CACHE_SRAM_USR_WCMD_R {
        CACHE_SRAM_USR_WCMD_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - reserved"]
    #[inline(always)]
    pub fn sram_oct(&self) -> SRAM_OCT_R {
        SRAM_OCT_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bits 22:27 - For SPI0, In the external RAM mode, it is the length in bits of write dummy phase. The register value shall be (bit_num-1)."]
    #[inline(always)]
    pub fn sram_wdummy_cyclelen(&self) -> SRAM_WDUMMY_CYCLELEN_R {
        SRAM_WDUMMY_CYCLELEN_R::new(((self.bits >> 22) & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_SCTRL")
            .field("cache_usr_saddr_4byte", &self.cache_usr_saddr_4byte())
            .field("usr_sram_dio", &self.usr_sram_dio())
            .field("usr_sram_qio", &self.usr_sram_qio())
            .field("usr_wr_sram_dummy", &self.usr_wr_sram_dummy())
            .field("usr_rd_sram_dummy", &self.usr_rd_sram_dummy())
            .field("cache_sram_usr_rcmd", &self.cache_sram_usr_rcmd())
            .field("sram_rdummy_cyclelen", &self.sram_rdummy_cyclelen())
            .field("sram_addr_bitlen", &self.sram_addr_bitlen())
            .field("cache_sram_usr_wcmd", &self.cache_sram_usr_wcmd())
            .field("sram_oct", &self.sram_oct())
            .field("sram_wdummy_cyclelen", &self.sram_wdummy_cyclelen())
            .finish()
    }
}
#[doc = "SPI0 external RAM control register\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_sctrl::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_SCTRL_SPEC;
impl crate::RegisterSpec for CACHE_SCTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_sctrl::R`](R) reader structure"]
impl crate::Readable for CACHE_SCTRL_SPEC {}
#[doc = "`reset()` method sets CACHE_SCTRL to value 0x0055_c070"]
impl crate::Resettable for CACHE_SCTRL_SPEC {
    const RESET_VALUE: u32 = 0x0055_c070;
}
