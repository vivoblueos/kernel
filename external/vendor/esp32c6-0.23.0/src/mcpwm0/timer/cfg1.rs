#[doc = "Register `CFG1` reader"]
pub type R = crate::R<CFG1_SPEC>;
#[doc = "Register `CFG1` writer"]
pub type W = crate::W<CFG1_SPEC>;
#[doc = "Field `START` reader - PWM timer0 start and stop control. 0: if PWM timer0 starts, then stops at TEZ, 1: if timer0 starts, then stops at TEP, 2: PWM timer0 starts and runs on, 3: timer0 starts and stops at the next TEZ, 4: timer0 starts and stops at the next TEP. TEP here and below means the event that happens when the timer equals to period"]
pub type START_R = crate::FieldReader;
#[doc = "Field `START` writer - PWM timer0 start and stop control. 0: if PWM timer0 starts, then stops at TEZ, 1: if timer0 starts, then stops at TEP, 2: PWM timer0 starts and runs on, 3: timer0 starts and stops at the next TEZ, 4: timer0 starts and stops at the next TEP. TEP here and below means the event that happens when the timer equals to period"]
pub type START_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `MOD` reader - PWM timer0 working mode, 0: freeze, 1: increase mode, 2: decrease mode, 3: up-down mode"]
pub type MOD_R = crate::FieldReader;
#[doc = "Field `MOD` writer - PWM timer0 working mode, 0: freeze, 1: increase mode, 2: decrease mode, 3: up-down mode"]
pub type MOD_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:2 - PWM timer0 start and stop control. 0: if PWM timer0 starts, then stops at TEZ, 1: if timer0 starts, then stops at TEP, 2: PWM timer0 starts and runs on, 3: timer0 starts and stops at the next TEZ, 4: timer0 starts and stops at the next TEP. TEP here and below means the event that happens when the timer equals to period"]
    #[inline(always)]
    pub fn start(&self) -> START_R {
        START_R::new((self.bits & 7) as u8)
    }
    #[doc = "Bits 3:4 - PWM timer0 working mode, 0: freeze, 1: increase mode, 2: decrease mode, 3: up-down mode"]
    #[inline(always)]
    pub fn mod_(&self) -> MOD_R {
        MOD_R::new(((self.bits >> 3) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CFG1")
            .field("start", &self.start())
            .field("mod_", &self.mod_())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:2 - PWM timer0 start and stop control. 0: if PWM timer0 starts, then stops at TEZ, 1: if timer0 starts, then stops at TEP, 2: PWM timer0 starts and runs on, 3: timer0 starts and stops at the next TEZ, 4: timer0 starts and stops at the next TEP. TEP here and below means the event that happens when the timer equals to period"]
    #[inline(always)]
    pub fn start(&mut self) -> START_W<'_, CFG1_SPEC> {
        START_W::new(self, 0)
    }
    #[doc = "Bits 3:4 - PWM timer0 working mode, 0: freeze, 1: increase mode, 2: decrease mode, 3: up-down mode"]
    #[inline(always)]
    pub fn mod_(&mut self) -> MOD_W<'_, CFG1_SPEC> {
        MOD_W::new(self, 3)
    }
}
#[doc = "PWM TIMERx working mode and start/stop control configuration register.\n\nYou can [`read`](crate::Reg::read) this register and get [`cfg1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cfg1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CFG1_SPEC;
impl crate::RegisterSpec for CFG1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cfg1::R`](R) reader structure"]
impl crate::Readable for CFG1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cfg1::W`](W) writer structure"]
impl crate::Writable for CFG1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CFG1 to value 0"]
impl crate::Resettable for CFG1_SPEC {}
