#[doc = "Register `SYNC` reader"]
pub type R = crate::R<SYNC_SPEC>;
#[doc = "Register `SYNC` writer"]
pub type W = crate::W<SYNC_SPEC>;
#[doc = "Field `SYNCI_EN` reader - When set, timer reloading with phase on sync input event is enabled."]
pub type SYNCI_EN_R = crate::BitReader;
#[doc = "Field `SYNCI_EN` writer - When set, timer reloading with phase on sync input event is enabled."]
pub type SYNCI_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SW` reader - Toggling this bit will trigger a software sync."]
pub type SW_R = crate::BitReader;
#[doc = "Field `SW` writer - Toggling this bit will trigger a software sync."]
pub type SW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SYNCO_SEL` reader - PWM timer0 sync_out selection, 0: sync_in, 1: TEZ, 2: TEP, and sync out will always generate when toggling the reg_timer0_sync_sw bit"]
pub type SYNCO_SEL_R = crate::FieldReader;
#[doc = "Field `SYNCO_SEL` writer - PWM timer0 sync_out selection, 0: sync_in, 1: TEZ, 2: TEP, and sync out will always generate when toggling the reg_timer0_sync_sw bit"]
pub type SYNCO_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PHASE` reader - phase for timer reload on sync event"]
pub type PHASE_R = crate::FieldReader<u16>;
#[doc = "Field `PHASE` writer - phase for timer reload on sync event"]
pub type PHASE_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `PHASE_DIRECTION` reader - Configure the PWM timer0's direction when timer0 mode is up-down mode: 0-increase,1-decrease"]
pub type PHASE_DIRECTION_R = crate::BitReader;
#[doc = "Field `PHASE_DIRECTION` writer - Configure the PWM timer0's direction when timer0 mode is up-down mode: 0-increase,1-decrease"]
pub type PHASE_DIRECTION_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - When set, timer reloading with phase on sync input event is enabled."]
    #[inline(always)]
    pub fn synci_en(&self) -> SYNCI_EN_R {
        SYNCI_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Toggling this bit will trigger a software sync."]
    #[inline(always)]
    pub fn sw(&self) -> SW_R {
        SW_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:3 - PWM timer0 sync_out selection, 0: sync_in, 1: TEZ, 2: TEP, and sync out will always generate when toggling the reg_timer0_sync_sw bit"]
    #[inline(always)]
    pub fn synco_sel(&self) -> SYNCO_SEL_R {
        SYNCO_SEL_R::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:19 - phase for timer reload on sync event"]
    #[inline(always)]
    pub fn phase(&self) -> PHASE_R {
        PHASE_R::new(((self.bits >> 4) & 0xffff) as u16)
    }
    #[doc = "Bit 20 - Configure the PWM timer0's direction when timer0 mode is up-down mode: 0-increase,1-decrease"]
    #[inline(always)]
    pub fn phase_direction(&self) -> PHASE_DIRECTION_R {
        PHASE_DIRECTION_R::new(((self.bits >> 20) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SYNC")
            .field("synci_en", &self.synci_en())
            .field("sw", &self.sw())
            .field("synco_sel", &self.synco_sel())
            .field("phase", &self.phase())
            .field("phase_direction", &self.phase_direction())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - When set, timer reloading with phase on sync input event is enabled."]
    #[inline(always)]
    pub fn synci_en(&mut self) -> SYNCI_EN_W<'_, SYNC_SPEC> {
        SYNCI_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Toggling this bit will trigger a software sync."]
    #[inline(always)]
    pub fn sw(&mut self) -> SW_W<'_, SYNC_SPEC> {
        SW_W::new(self, 1)
    }
    #[doc = "Bits 2:3 - PWM timer0 sync_out selection, 0: sync_in, 1: TEZ, 2: TEP, and sync out will always generate when toggling the reg_timer0_sync_sw bit"]
    #[inline(always)]
    pub fn synco_sel(&mut self) -> SYNCO_SEL_W<'_, SYNC_SPEC> {
        SYNCO_SEL_W::new(self, 2)
    }
    #[doc = "Bits 4:19 - phase for timer reload on sync event"]
    #[inline(always)]
    pub fn phase(&mut self) -> PHASE_W<'_, SYNC_SPEC> {
        PHASE_W::new(self, 4)
    }
    #[doc = "Bit 20 - Configure the PWM timer0's direction when timer0 mode is up-down mode: 0-increase,1-decrease"]
    #[inline(always)]
    pub fn phase_direction(&mut self) -> PHASE_DIRECTION_W<'_, SYNC_SPEC> {
        PHASE_DIRECTION_W::new(self, 20)
    }
}
#[doc = "PWM TIMERx sync function configuration register.\n\nYou can [`read`](crate::Reg::read) this register and get [`sync::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sync::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SYNC_SPEC;
impl crate::RegisterSpec for SYNC_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sync::R`](R) reader structure"]
impl crate::Readable for SYNC_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sync::W`](W) writer structure"]
impl crate::Writable for SYNC_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SYNC to value 0"]
impl crate::Resettable for SYNC_SPEC {}
