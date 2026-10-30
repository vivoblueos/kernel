#[doc = "Register `XTS_STATE` reader"]
pub type R = crate::R<XTS_STATE_SPEC>;
#[doc = "Field `SPI_XTS_STATE` reader - This bits stores the status of manual encryption. 0: idle, 1: busy of encryption calculation, 2: encryption calculation is done but the encrypted result is invisible to mspi, 3: the encrypted result is visible to mspi."]
pub type SPI_XTS_STATE_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:1 - This bits stores the status of manual encryption. 0: idle, 1: busy of encryption calculation, 2: encryption calculation is done but the encrypted result is invisible to mspi, 3: the encrypted result is visible to mspi."]
    #[inline(always)]
    pub fn spi_xts_state(&self) -> SPI_XTS_STATE_R {
        SPI_XTS_STATE_R::new((self.bits & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("XTS_STATE")
            .field("spi_xts_state", &self.spi_xts_state())
            .finish()
    }
}
#[doc = "Manual Encryption physical address register\n\nYou can [`read`](crate::Reg::read) this register and get [`xts_state::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct XTS_STATE_SPEC;
impl crate::RegisterSpec for XTS_STATE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`xts_state::R`](R) reader structure"]
impl crate::Readable for XTS_STATE_SPEC {}
#[doc = "`reset()` method sets XTS_STATE to value 0"]
impl crate::Resettable for XTS_STATE_SPEC {}
