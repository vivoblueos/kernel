#[doc = "Register `CRC_ERROR_CNT` reader"]
pub type R = crate::R<CRC_ERROR_CNT_SPEC>;
#[doc = "Register `CRC_ERROR_CNT` writer"]
pub type W = crate::W<CRC_ERROR_CNT_SPEC>;
#[doc = "Field `CRC_ERROR_CNT` reader - "]
pub type CRC_ERROR_CNT_R = crate::FieldReader<u16>;
#[doc = "Field `CRC_ERROR_CNT` writer - "]
pub type CRC_ERROR_CNT_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn crc_error_cnt(&self) -> CRC_ERROR_CNT_R {
        CRC_ERROR_CNT_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CRC_ERROR_CNT")
            .field("crc_error_cnt", &self.crc_error_cnt())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn crc_error_cnt(&mut self) -> CRC_ERROR_CNT_W<'_, CRC_ERROR_CNT_SPEC> {
        CRC_ERROR_CNT_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`crc_error_cnt::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`crc_error_cnt::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CRC_ERROR_CNT_SPEC;
impl crate::RegisterSpec for CRC_ERROR_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`crc_error_cnt::R`](R) reader structure"]
impl crate::Readable for CRC_ERROR_CNT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`crc_error_cnt::W`](W) writer structure"]
impl crate::Writable for CRC_ERROR_CNT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CRC_ERROR_CNT to value 0"]
impl crate::Resettable for CRC_ERROR_CNT_SPEC {}
