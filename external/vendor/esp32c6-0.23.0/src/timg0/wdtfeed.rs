#[doc = "Register `WDTFEED` writer"]
pub type W = crate::W<WDTFEED_SPEC>;
#[doc = "Field `WDT_FEED` writer - Write any value to feed the MWDT. (WO)"]
pub type WDT_FEED_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<WDTFEED_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bits 0:31 - Write any value to feed the MWDT. (WO)"]
    #[inline(always)]
    pub fn wdt_feed(&mut self) -> WDT_FEED_W<'_, WDTFEED_SPEC> {
        WDT_FEED_W::new(self, 0)
    }
}
#[doc = "Write to feed the watchdog timer\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wdtfeed::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct WDTFEED_SPEC;
impl crate::RegisterSpec for WDTFEED_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`wdtfeed::W`](W) writer structure"]
impl crate::Writable for WDTFEED_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets WDTFEED to value 0"]
impl crate::Resettable for WDTFEED_SPEC {}
