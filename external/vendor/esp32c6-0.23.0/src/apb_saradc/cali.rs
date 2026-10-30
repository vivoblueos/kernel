#[doc = "Register `CALI` reader"]
pub type R = crate::R<CALI_SPEC>;
#[doc = "Register `CALI` writer"]
pub type W = crate::W<CALI_SPEC>;
#[doc = "Field `CFG` reader - saradc cali factor"]
pub type CFG_R = crate::FieldReader<u32>;
#[doc = "Field `CFG` writer - saradc cali factor"]
pub type CFG_W<'a, REG> = crate::FieldWriter<'a, REG, 17, u32>;
impl R {
    #[doc = "Bits 0:16 - saradc cali factor"]
    #[inline(always)]
    pub fn cfg(&self) -> CFG_R {
        CFG_R::new(self.bits & 0x0001_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CALI").field("cfg", &self.cfg()).finish()
    }
}
impl W {
    #[doc = "Bits 0:16 - saradc cali factor"]
    #[inline(always)]
    pub fn cfg(&mut self) -> CFG_W<'_, CALI_SPEC> {
        CFG_W::new(self, 0)
    }
}
#[doc = "digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`cali::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cali::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CALI_SPEC;
impl crate::RegisterSpec for CALI_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cali::R`](R) reader structure"]
impl crate::Readable for CALI_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cali::W`](W) writer structure"]
impl crate::Writable for CALI_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CALI to value 0x8000"]
impl crate::Resettable for CALI_SPEC {
    const RESET_VALUE: u32 = 0x8000;
}
