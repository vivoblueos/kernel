#[doc = "Register `TX_CRC` reader"]
pub type R = crate::R<TX_CRC_SPEC>;
#[doc = "Field `DATA` reader - For SPI1, the value of crc32."]
pub type DATA_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - For SPI1, the value of crc32."]
    #[inline(always)]
    pub fn data(&self) -> DATA_R {
        DATA_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_CRC")
            .field("data", &self.data())
            .finish()
    }
}
#[doc = "SPI1 TX CRC data register.\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_crc::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_CRC_SPEC;
impl crate::RegisterSpec for TX_CRC_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_crc::R`](R) reader structure"]
impl crate::Readable for TX_CRC_SPEC {}
#[doc = "`reset()` method sets TX_CRC to value 0xffff_ffff"]
impl crate::Resettable for TX_CRC_SPEC {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
