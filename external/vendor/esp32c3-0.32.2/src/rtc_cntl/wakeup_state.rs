#[doc = "Register `WAKEUP_STATE` reader"]
pub type R = crate::R<WAKEUP_STATE_SPEC>;
#[doc = "Register `WAKEUP_STATE` writer"]
pub type W = crate::W<WAKEUP_STATE_SPEC>;
#[doc = "Field `WAKEUP_ENA` reader - wakeup enable bitmap"]
pub type WAKEUP_ENA_R = crate::FieldReader<u32>;
#[doc = "Field `WAKEUP_ENA` writer - wakeup enable bitmap"]
pub type WAKEUP_ENA_W<'a, REG> = crate::FieldWriter<'a, REG, 17, u32>;
impl R {
    #[doc = "Bits 15:31 - wakeup enable bitmap"]
    #[inline(always)]
    pub fn wakeup_ena(&self) -> WAKEUP_ENA_R {
        WAKEUP_ENA_R::new((self.bits >> 15) & 0x0001_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("WAKEUP_STATE")
            .field("wakeup_ena", &self.wakeup_ena())
            .finish()
    }
}
impl W {
    #[doc = "Bits 15:31 - wakeup enable bitmap"]
    #[inline(always)]
    pub fn wakeup_ena(&mut self) -> WAKEUP_ENA_W<'_, WAKEUP_STATE_SPEC> {
        WAKEUP_ENA_W::new(self, 15)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`wakeup_state::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wakeup_state::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct WAKEUP_STATE_SPEC;
impl crate::RegisterSpec for WAKEUP_STATE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`wakeup_state::R`](R) reader structure"]
impl crate::Readable for WAKEUP_STATE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`wakeup_state::W`](W) writer structure"]
impl crate::Writable for WAKEUP_STATE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets WAKEUP_STATE to value 0x0006_0000"]
impl crate::Resettable for WAKEUP_STATE_SPEC {
    const RESET_VALUE: u32 = 0x0006_0000;
}
