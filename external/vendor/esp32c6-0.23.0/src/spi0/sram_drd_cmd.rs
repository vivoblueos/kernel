#[doc = "Register `SRAM_DRD_CMD` reader"]
pub type R = crate::R<SRAM_DRD_CMD_SPEC>;
#[doc = "Field `CACHE_SRAM_USR_RD_CMD_VALUE` reader - For SPI0,When cache mode is enable it is the read command value of command phase for sram."]
pub type CACHE_SRAM_USR_RD_CMD_VALUE_R = crate::FieldReader<u16>;
#[doc = "Field `CACHE_SRAM_USR_RD_CMD_BITLEN` reader - For SPI0,When cache mode is enable it is the length in bits of command phase for sram. The register value shall be (bit_num-1)."]
pub type CACHE_SRAM_USR_RD_CMD_BITLEN_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:15 - For SPI0,When cache mode is enable it is the read command value of command phase for sram."]
    #[inline(always)]
    pub fn cache_sram_usr_rd_cmd_value(&self) -> CACHE_SRAM_USR_RD_CMD_VALUE_R {
        CACHE_SRAM_USR_RD_CMD_VALUE_R::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 28:31 - For SPI0,When cache mode is enable it is the length in bits of command phase for sram. The register value shall be (bit_num-1)."]
    #[inline(always)]
    pub fn cache_sram_usr_rd_cmd_bitlen(&self) -> CACHE_SRAM_USR_RD_CMD_BITLEN_R {
        CACHE_SRAM_USR_RD_CMD_BITLEN_R::new(((self.bits >> 28) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SRAM_DRD_CMD")
            .field(
                "cache_sram_usr_rd_cmd_value",
                &self.cache_sram_usr_rd_cmd_value(),
            )
            .field(
                "cache_sram_usr_rd_cmd_bitlen",
                &self.cache_sram_usr_rd_cmd_bitlen(),
            )
            .finish()
    }
}
#[doc = "SPI0 external RAM DDR read command control register\n\nYou can [`read`](crate::Reg::read) this register and get [`sram_drd_cmd::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SRAM_DRD_CMD_SPEC;
impl crate::RegisterSpec for SRAM_DRD_CMD_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sram_drd_cmd::R`](R) reader structure"]
impl crate::Readable for SRAM_DRD_CMD_SPEC {}
#[doc = "`reset()` method sets SRAM_DRD_CMD to value 0"]
impl crate::Resettable for SRAM_DRD_CMD_SPEC {}
