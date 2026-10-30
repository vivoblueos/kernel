#[doc = "Register `CCA_BUSY_CNT` reader"]
pub type R = crate::R<CCA_BUSY_CNT_SPEC>;
#[doc = "Register `CCA_BUSY_CNT` writer"]
pub type W = crate::W<CCA_BUSY_CNT_SPEC>;
#[doc = "Field `CCA_BUSY_CNT` reader - "]
pub type CCA_BUSY_CNT_R = crate::FieldReader<u16>;
#[doc = "Field `CCA_BUSY_CNT` writer - "]
pub type CCA_BUSY_CNT_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn cca_busy_cnt(&self) -> CCA_BUSY_CNT_R {
        CCA_BUSY_CNT_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CCA_BUSY_CNT")
            .field("cca_busy_cnt", &self.cca_busy_cnt())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn cca_busy_cnt(&mut self) -> CCA_BUSY_CNT_W<'_, CCA_BUSY_CNT_SPEC> {
        CCA_BUSY_CNT_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`cca_busy_cnt::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cca_busy_cnt::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CCA_BUSY_CNT_SPEC;
impl crate::RegisterSpec for CCA_BUSY_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cca_busy_cnt::R`](R) reader structure"]
impl crate::Readable for CCA_BUSY_CNT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cca_busy_cnt::W`](W) writer structure"]
impl crate::Writable for CCA_BUSY_CNT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CCA_BUSY_CNT to value 0"]
impl crate::Resettable for CCA_BUSY_CNT_SPEC {}
