#[doc = "Register `HI` reader"]
pub type R = crate::R<HI_SPEC>;
#[doc = "Register `HI` writer"]
pub type W = crate::W<HI_SPEC>;
#[doc = "Field `LOAD_HI` reader - timer unit0 load high 32 bit"]
pub type LOAD_HI_R = crate::FieldReader<u32>;
#[doc = "Field `LOAD_HI` writer - timer unit0 load high 32 bit"]
pub type LOAD_HI_W<'a, REG> = crate::FieldWriter<'a, REG, 20, u32, crate::Safe>;
impl R {
    #[doc = "Bits 0:19 - timer unit0 load high 32 bit"]
    #[inline(always)]
    pub fn load_hi(&self) -> LOAD_HI_R {
        LOAD_HI_R::new(self.bits & 0x000f_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HI")
            .field("load_hi", &self.load_hi())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:19 - timer unit0 load high 32 bit"]
    #[inline(always)]
    pub fn load_hi(&mut self) -> LOAD_HI_W<'_, HI_SPEC> {
        LOAD_HI_W::new(self, 0)
    }
}
#[doc = "SYSTIMER_UNIT0_LOAD_HI.\n\nYou can [`read`](crate::Reg::read) this register and get [`hi::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hi::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HI_SPEC;
impl crate::RegisterSpec for HI_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hi::R`](R) reader structure"]
impl crate::Readable for HI_SPEC {}
#[doc = "`write(|w| ..)` method takes [`hi::W`](W) writer structure"]
impl crate::Writable for HI_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HI to value 0"]
impl crate::Resettable for HI_SPEC {}
