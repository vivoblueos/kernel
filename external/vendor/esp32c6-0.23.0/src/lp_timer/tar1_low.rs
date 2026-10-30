#[doc = "Register `TAR1_LOW` reader"]
pub type R = crate::R<TAR1_LOW_SPEC>;
#[doc = "Register `TAR1_LOW` writer"]
pub type W = crate::W<TAR1_LOW_SPEC>;
#[doc = "Field `MAIN_TIMER_TAR_LOW1` reader - need_des"]
pub type MAIN_TIMER_TAR_LOW1_R = crate::FieldReader<u32>;
#[doc = "Field `MAIN_TIMER_TAR_LOW1` writer - need_des"]
pub type MAIN_TIMER_TAR_LOW1_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn main_timer_tar_low1(&self) -> MAIN_TIMER_TAR_LOW1_R {
        MAIN_TIMER_TAR_LOW1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TAR1_LOW")
            .field("main_timer_tar_low1", &self.main_timer_tar_low1())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn main_timer_tar_low1(&mut self) -> MAIN_TIMER_TAR_LOW1_W<'_, TAR1_LOW_SPEC> {
        MAIN_TIMER_TAR_LOW1_W::new(self, 0)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`tar1_low::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tar1_low::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TAR1_LOW_SPEC;
impl crate::RegisterSpec for TAR1_LOW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tar1_low::R`](R) reader structure"]
impl crate::Readable for TAR1_LOW_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tar1_low::W`](W) writer structure"]
impl crate::Writable for TAR1_LOW_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TAR1_LOW to value 0"]
impl crate::Resettable for TAR1_LOW_SPEC {}
