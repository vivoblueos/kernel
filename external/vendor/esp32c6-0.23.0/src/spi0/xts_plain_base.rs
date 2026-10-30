#[doc = "Register `XTS_PLAIN_BASE` reader"]
pub type R = crate::R<XTS_PLAIN_BASE_SPEC>;
#[doc = "Register `XTS_PLAIN_BASE` writer"]
pub type W = crate::W<XTS_PLAIN_BASE_SPEC>;
#[doc = "Field `SPI_XTS_PLAIN` reader - This field is only used to generate include file in c case. This field is useless. Please do not use this field."]
pub type SPI_XTS_PLAIN_R = crate::FieldReader<u32>;
#[doc = "Field `SPI_XTS_PLAIN` writer - This field is only used to generate include file in c case. This field is useless. Please do not use this field."]
pub type SPI_XTS_PLAIN_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - This field is only used to generate include file in c case. This field is useless. Please do not use this field."]
    #[inline(always)]
    pub fn spi_xts_plain(&self) -> SPI_XTS_PLAIN_R {
        SPI_XTS_PLAIN_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("XTS_PLAIN_BASE")
            .field("spi_xts_plain", &self.spi_xts_plain())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - This field is only used to generate include file in c case. This field is useless. Please do not use this field."]
    #[inline(always)]
    pub fn spi_xts_plain(&mut self) -> SPI_XTS_PLAIN_W<'_, XTS_PLAIN_BASE_SPEC> {
        SPI_XTS_PLAIN_W::new(self, 0)
    }
}
#[doc = "The base address of the memory that stores plaintext in Manual Encryption\n\nYou can [`read`](crate::Reg::read) this register and get [`xts_plain_base::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`xts_plain_base::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct XTS_PLAIN_BASE_SPEC;
impl crate::RegisterSpec for XTS_PLAIN_BASE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`xts_plain_base::R`](R) reader structure"]
impl crate::Readable for XTS_PLAIN_BASE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`xts_plain_base::W`](W) writer structure"]
impl crate::Writable for XTS_PLAIN_BASE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets XTS_PLAIN_BASE to value 0"]
impl crate::Resettable for XTS_PLAIN_BASE_SPEC {}
