#[doc = "Register `HPOINT` reader"]
pub type R = crate::R<HPOINT_SPEC>;
#[doc = "Register `HPOINT` writer"]
pub type W = crate::W<HPOINT_SPEC>;
#[doc = "Field `HPOINT` reader - The output value changes to high when the selected timers has reached the value specified by this register."]
pub type HPOINT_R = crate::FieldReader<u32>;
#[doc = "Field `HPOINT` writer - The output value changes to high when the selected timers has reached the value specified by this register."]
pub type HPOINT_W<'a, REG> = crate::FieldWriter<'a, REG, 20, u32>;
impl R {
    #[doc = "Bits 0:19 - The output value changes to high when the selected timers has reached the value specified by this register."]
    #[inline(always)]
    pub fn hpoint(&self) -> HPOINT_R {
        HPOINT_R::new(self.bits & 0x000f_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HPOINT")
            .field("hpoint", &self.hpoint())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:19 - The output value changes to high when the selected timers has reached the value specified by this register."]
    #[inline(always)]
    pub fn hpoint(&mut self) -> HPOINT_W<'_, HPOINT_SPEC> {
        HPOINT_W::new(self, 0)
    }
}
#[doc = "High point register for channel 0\n\nYou can [`read`](crate::Reg::read) this register and get [`hpoint::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hpoint::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HPOINT_SPEC;
impl crate::RegisterSpec for HPOINT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hpoint::R`](R) reader structure"]
impl crate::Readable for HPOINT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`hpoint::W`](W) writer structure"]
impl crate::Writable for HPOINT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HPOINT to value 0"]
impl crate::Resettable for HPOINT_SPEC {}
