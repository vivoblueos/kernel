#[doc = "Register `WDT2` reader"]
pub type R = crate::R<Wdt2Spec>;
#[doc = "Register `WDT2` writer"]
pub type W = crate::W<Wdt2Spec>;
#[doc = "Field `WDLT2` reader - Analog watchdog 2 low threshold"]
pub type Wdlt2R = crate::FieldReader;
#[doc = "Field `WDLT2` writer - Analog watchdog 2 low threshold"]
pub type Wdlt2W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `WDHT2` reader - Analog watchdog 2 high threshold"]
pub type Wdht2R = crate::FieldReader;
#[doc = "Field `WDHT2` writer - Analog watchdog 2 high threshold"]
pub type Wdht2W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - Analog watchdog 2 low threshold"]
    #[inline(always)]
    pub fn wdlt2(&self) -> Wdlt2R {
        Wdlt2R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - Analog watchdog 2 high threshold"]
    #[inline(always)]
    pub fn wdht2(&self) -> Wdht2R {
        Wdht2R::new(((self.bits >> 16) & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:7 - Analog watchdog 2 low threshold"]
    #[inline(always)]
    #[must_use]
    pub fn wdlt2(&mut self) -> Wdlt2W<Wdt2Spec> {
        Wdlt2W::new(self, 0)
    }
    #[doc = "Bits 16:23 - Analog watchdog 2 high threshold"]
    #[inline(always)]
    #[must_use]
    pub fn wdht2(&mut self) -> Wdht2W<Wdt2Spec> {
        Wdht2W::new(self, 16)
    }
}
#[doc = "Watchdog threshold register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`wdt2::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`wdt2::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Wdt2Spec;
impl crate::RegisterSpec for Wdt2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`wdt2::R`](R) reader structure"]
impl crate::Readable for Wdt2Spec {}
#[doc = "`write(|w| ..)` method takes [`wdt2::W`](W) writer structure"]
impl crate::Writable for Wdt2Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets WDT2 to value 0x00ff_0000"]
impl crate::Resettable for Wdt2Spec {
    const RESET_VALUE: u32 = 0x00ff_0000;
}
