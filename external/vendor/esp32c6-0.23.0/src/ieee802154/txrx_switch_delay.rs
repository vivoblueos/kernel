#[doc = "Register `TXRX_SWITCH_DELAY` reader"]
pub type R = crate::R<TXRX_SWITCH_DELAY_SPEC>;
#[doc = "Register `TXRX_SWITCH_DELAY` writer"]
pub type W = crate::W<TXRX_SWITCH_DELAY_SPEC>;
#[doc = "Field `TXRX_SWITCH_DELAY` reader - "]
pub type TXRX_SWITCH_DELAY_R = crate::FieldReader<u16>;
#[doc = "Field `TXRX_SWITCH_DELAY` writer - "]
pub type TXRX_SWITCH_DELAY_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
impl R {
    #[doc = "Bits 0:9"]
    #[inline(always)]
    pub fn txrx_switch_delay(&self) -> TXRX_SWITCH_DELAY_R {
        TXRX_SWITCH_DELAY_R::new((self.bits & 0x03ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TXRX_SWITCH_DELAY")
            .field("txrx_switch_delay", &self.txrx_switch_delay())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:9"]
    #[inline(always)]
    pub fn txrx_switch_delay(&mut self) -> TXRX_SWITCH_DELAY_W<'_, TXRX_SWITCH_DELAY_SPEC> {
        TXRX_SWITCH_DELAY_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`txrx_switch_delay::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txrx_switch_delay::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TXRX_SWITCH_DELAY_SPEC;
impl crate::RegisterSpec for TXRX_SWITCH_DELAY_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`txrx_switch_delay::R`](R) reader structure"]
impl crate::Readable for TXRX_SWITCH_DELAY_SPEC {}
#[doc = "`write(|w| ..)` method takes [`txrx_switch_delay::W`](W) writer structure"]
impl crate::Writable for TXRX_SWITCH_DELAY_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TXRX_SWITCH_DELAY to value 0"]
impl crate::Resettable for TXRX_SWITCH_DELAY_SPEC {}
