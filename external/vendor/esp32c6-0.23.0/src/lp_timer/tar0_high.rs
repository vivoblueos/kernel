#[doc = "Register `TAR0_HIGH` reader"]
pub type R = crate::R<TAR0_HIGH_SPEC>;
#[doc = "Register `TAR0_HIGH` writer"]
pub type W = crate::W<TAR0_HIGH_SPEC>;
#[doc = "Field `MAIN_TIMER_TAR_HIGH0` reader - need_des"]
pub type MAIN_TIMER_TAR_HIGH0_R = crate::FieldReader<u16>;
#[doc = "Field `MAIN_TIMER_TAR_HIGH0` writer - need_des"]
pub type MAIN_TIMER_TAR_HIGH0_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `MAIN_TIMER_TAR_EN0` writer - need_des"]
pub type MAIN_TIMER_TAR_EN0_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:15 - need_des"]
    #[inline(always)]
    pub fn main_timer_tar_high0(&self) -> MAIN_TIMER_TAR_HIGH0_R {
        MAIN_TIMER_TAR_HIGH0_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TAR0_HIGH")
            .field("main_timer_tar_high0", &self.main_timer_tar_high0())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - need_des"]
    #[inline(always)]
    pub fn main_timer_tar_high0(&mut self) -> MAIN_TIMER_TAR_HIGH0_W<'_, TAR0_HIGH_SPEC> {
        MAIN_TIMER_TAR_HIGH0_W::new(self, 0)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn main_timer_tar_en0(&mut self) -> MAIN_TIMER_TAR_EN0_W<'_, TAR0_HIGH_SPEC> {
        MAIN_TIMER_TAR_EN0_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`tar0_high::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tar0_high::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TAR0_HIGH_SPEC;
impl crate::RegisterSpec for TAR0_HIGH_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tar0_high::R`](R) reader structure"]
impl crate::Readable for TAR0_HIGH_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tar0_high::W`](W) writer structure"]
impl crate::Writable for TAR0_HIGH_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TAR0_HIGH to value 0"]
impl crate::Resettable for TAR0_HIGH_SPEC {}
