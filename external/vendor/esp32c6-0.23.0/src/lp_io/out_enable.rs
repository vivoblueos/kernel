#[doc = "Register `OUT_ENABLE` reader"]
pub type R = crate::R<OUT_ENABLE_SPEC>;
#[doc = "Register `OUT_ENABLE` writer"]
pub type W = crate::W<OUT_ENABLE_SPEC>;
#[doc = "Field `ENABLE` reader - set lp gpio output data"]
pub type ENABLE_R = crate::FieldReader;
#[doc = "Field `ENABLE` writer - set lp gpio output data"]
pub type ENABLE_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - set lp gpio output data"]
    #[inline(always)]
    pub fn enable(&self) -> ENABLE_R {
        ENABLE_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("OUT_ENABLE")
            .field("enable", &self.enable())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - set lp gpio output data"]
    #[inline(always)]
    pub fn enable(&mut self) -> ENABLE_W<'_, OUT_ENABLE_SPEC> {
        ENABLE_W::new(self, 0)
    }
}
#[doc = "need des\n\nYou can [`read`](crate::Reg::read) this register and get [`out_enable::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_enable::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OUT_ENABLE_SPEC;
impl crate::RegisterSpec for OUT_ENABLE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`out_enable::R`](R) reader structure"]
impl crate::Readable for OUT_ENABLE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`out_enable::W`](W) writer structure"]
impl crate::Writable for OUT_ENABLE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets OUT_ENABLE to value 0"]
impl crate::Resettable for OUT_ENABLE_SPEC {}
