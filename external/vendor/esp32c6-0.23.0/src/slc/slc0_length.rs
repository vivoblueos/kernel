#[doc = "Register `SLC0_LENGTH` reader"]
pub type R = crate::R<SLC0_LENGTH_SPEC>;
#[doc = "Field `SDIO_SLC0_LEN` reader - Represents the accumulated length of data that the slave wants to send."]
pub type SDIO_SLC0_LEN_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:19 - Represents the accumulated length of data that the slave wants to send."]
    #[inline(always)]
    pub fn sdio_slc0_len(&self) -> SDIO_SLC0_LEN_R {
        SDIO_SLC0_LEN_R::new(self.bits & 0x000f_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC0_LENGTH")
            .field("sdio_slc0_len", &self.sdio_slc0_len())
            .finish()
    }
}
#[doc = "Length of transmitting packets\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0_length::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC0_LENGTH_SPEC;
impl crate::RegisterSpec for SLC0_LENGTH_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc0_length::R`](R) reader structure"]
impl crate::Readable for SLC0_LENGTH_SPEC {}
#[doc = "`reset()` method sets SLC0_LENGTH to value 0"]
impl crate::Resettable for SLC0_LENGTH_SPEC {}
