#[doc = "Register `FAULT_DETECT` reader"]
pub type R = crate::R<FAULT_DETECT_SPEC>;
#[doc = "Register `FAULT_DETECT` writer"]
pub type W = crate::W<FAULT_DETECT_SPEC>;
#[doc = "Field `F0_EN` reader - When set, event_f0 generation is enabled"]
pub type F0_EN_R = crate::BitReader;
#[doc = "Field `F0_EN` writer - When set, event_f0 generation is enabled"]
pub type F0_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `F1_EN` reader - When set, event_f1 generation is enabled"]
pub type F1_EN_R = crate::BitReader;
#[doc = "Field `F1_EN` writer - When set, event_f1 generation is enabled"]
pub type F1_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `F2_EN` reader - When set, event_f2 generation is enabled"]
pub type F2_EN_R = crate::BitReader;
#[doc = "Field `F2_EN` writer - When set, event_f2 generation is enabled"]
pub type F2_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `F0_POLE` reader - Set event_f0 trigger polarity on FAULT2 source from GPIO matrix. 0: level low, 1: level high"]
pub type F0_POLE_R = crate::BitReader;
#[doc = "Field `F0_POLE` writer - Set event_f0 trigger polarity on FAULT2 source from GPIO matrix. 0: level low, 1: level high"]
pub type F0_POLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `F1_POLE` reader - Set event_f1 trigger polarity on FAULT2 source from GPIO matrix. 0: level low, 1: level high"]
pub type F1_POLE_R = crate::BitReader;
#[doc = "Field `F1_POLE` writer - Set event_f1 trigger polarity on FAULT2 source from GPIO matrix. 0: level low, 1: level high"]
pub type F1_POLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `F2_POLE` reader - Set event_f2 trigger polarity on FAULT2 source from GPIO matrix. 0: level low, 1: level high"]
pub type F2_POLE_R = crate::BitReader;
#[doc = "Field `F2_POLE` writer - Set event_f2 trigger polarity on FAULT2 source from GPIO matrix. 0: level low, 1: level high"]
pub type F2_POLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVENT_F0` reader - Set and reset by hardware. If set, event_f0 is on going"]
pub type EVENT_F0_R = crate::BitReader;
#[doc = "Field `EVENT_F1` reader - Set and reset by hardware. If set, event_f1 is on going"]
pub type EVENT_F1_R = crate::BitReader;
#[doc = "Field `EVENT_F2` reader - Set and reset by hardware. If set, event_f2 is on going"]
pub type EVENT_F2_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - When set, event_f0 generation is enabled"]
    #[inline(always)]
    pub fn f0_en(&self) -> F0_EN_R {
        F0_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - When set, event_f1 generation is enabled"]
    #[inline(always)]
    pub fn f1_en(&self) -> F1_EN_R {
        F1_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - When set, event_f2 generation is enabled"]
    #[inline(always)]
    pub fn f2_en(&self) -> F2_EN_R {
        F2_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Set event_f0 trigger polarity on FAULT2 source from GPIO matrix. 0: level low, 1: level high"]
    #[inline(always)]
    pub fn f0_pole(&self) -> F0_POLE_R {
        F0_POLE_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Set event_f1 trigger polarity on FAULT2 source from GPIO matrix. 0: level low, 1: level high"]
    #[inline(always)]
    pub fn f1_pole(&self) -> F1_POLE_R {
        F1_POLE_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Set event_f2 trigger polarity on FAULT2 source from GPIO matrix. 0: level low, 1: level high"]
    #[inline(always)]
    pub fn f2_pole(&self) -> F2_POLE_R {
        F2_POLE_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Set and reset by hardware. If set, event_f0 is on going"]
    #[inline(always)]
    pub fn event_f0(&self) -> EVENT_F0_R {
        EVENT_F0_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Set and reset by hardware. If set, event_f1 is on going"]
    #[inline(always)]
    pub fn event_f1(&self) -> EVENT_F1_R {
        EVENT_F1_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Set and reset by hardware. If set, event_f2 is on going"]
    #[inline(always)]
    pub fn event_f2(&self) -> EVENT_F2_R {
        EVENT_F2_R::new(((self.bits >> 8) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FAULT_DETECT")
            .field("f0_en", &self.f0_en())
            .field("f1_en", &self.f1_en())
            .field("f2_en", &self.f2_en())
            .field("f0_pole", &self.f0_pole())
            .field("f1_pole", &self.f1_pole())
            .field("f2_pole", &self.f2_pole())
            .field("event_f0", &self.event_f0())
            .field("event_f1", &self.event_f1())
            .field("event_f2", &self.event_f2())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - When set, event_f0 generation is enabled"]
    #[inline(always)]
    pub fn f0_en(&mut self) -> F0_EN_W<'_, FAULT_DETECT_SPEC> {
        F0_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - When set, event_f1 generation is enabled"]
    #[inline(always)]
    pub fn f1_en(&mut self) -> F1_EN_W<'_, FAULT_DETECT_SPEC> {
        F1_EN_W::new(self, 1)
    }
    #[doc = "Bit 2 - When set, event_f2 generation is enabled"]
    #[inline(always)]
    pub fn f2_en(&mut self) -> F2_EN_W<'_, FAULT_DETECT_SPEC> {
        F2_EN_W::new(self, 2)
    }
    #[doc = "Bit 3 - Set event_f0 trigger polarity on FAULT2 source from GPIO matrix. 0: level low, 1: level high"]
    #[inline(always)]
    pub fn f0_pole(&mut self) -> F0_POLE_W<'_, FAULT_DETECT_SPEC> {
        F0_POLE_W::new(self, 3)
    }
    #[doc = "Bit 4 - Set event_f1 trigger polarity on FAULT2 source from GPIO matrix. 0: level low, 1: level high"]
    #[inline(always)]
    pub fn f1_pole(&mut self) -> F1_POLE_W<'_, FAULT_DETECT_SPEC> {
        F1_POLE_W::new(self, 4)
    }
    #[doc = "Bit 5 - Set event_f2 trigger polarity on FAULT2 source from GPIO matrix. 0: level low, 1: level high"]
    #[inline(always)]
    pub fn f2_pole(&mut self) -> F2_POLE_W<'_, FAULT_DETECT_SPEC> {
        F2_POLE_W::new(self, 5)
    }
}
#[doc = "Fault detection configuration and status\n\nYou can [`read`](crate::Reg::read) this register and get [`fault_detect::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`fault_detect::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FAULT_DETECT_SPEC;
impl crate::RegisterSpec for FAULT_DETECT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fault_detect::R`](R) reader structure"]
impl crate::Readable for FAULT_DETECT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`fault_detect::W`](W) writer structure"]
impl crate::Writable for FAULT_DETECT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FAULT_DETECT to value 0"]
impl crate::Resettable for FAULT_DETECT_SPEC {}
