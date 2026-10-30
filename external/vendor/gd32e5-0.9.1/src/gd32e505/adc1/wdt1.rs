#[doc = "Register `WDT1` reader"]
pub type R = crate::R<Wdt1Spec>;
#[doc = "Register `WDT1` writer"]
pub type W = crate::W<Wdt1Spec>;
#[doc = "Field `WDLT1` reader - Analog watchdog 1 low threshold"]
pub type Wdlt1R = crate::FieldReader;
#[doc = "Field `WDLT1` writer - Analog watchdog 1 low threshold"]
pub type Wdlt1W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `WDHT1` reader - Analog watchdog 1 high threshold"]
pub type Wdht1R = crate::FieldReader;
#[doc = "Field `WDHT1` writer - Analog watchdog 1 high threshold"]
pub type Wdht1W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - Analog watchdog 1 low threshold"]
    #[inline(always)]
    pub fn wdlt1(&self) -> Wdlt1R {
        Wdlt1R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - Analog watchdog 1 high threshold"]
    #[inline(always)]
    pub fn wdht1(&self) -> Wdht1R {
        Wdht1R::new(((self.bits >> 16) & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:7 - Analog watchdog 1 low threshold"]
    #[inline(always)]
    #[must_use]
    pub fn wdlt1(&mut self) -> Wdlt1W<Wdt1Spec> {
        Wdlt1W::new(self, 0)
    }
    #[doc = "Bits 16:23 - Analog watchdog 1 high threshold"]
    #[inline(always)]
    #[must_use]
    pub fn wdht1(&mut self) -> Wdht1W<Wdt1Spec> {
        Wdht1W::new(self, 16)
    }
}
#[doc = "Watchdog threshold register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`wdt1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`wdt1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Wdt1Spec;
impl crate::RegisterSpec for Wdt1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`wdt1::R`](R) reader structure"]
impl crate::Readable for Wdt1Spec {}
#[doc = "`write(|w| ..)` method takes [`wdt1::W`](W) writer structure"]
impl crate::Writable for Wdt1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets WDT1 to value 0x00ff_0000"]
impl crate::Resettable for Wdt1Spec {
    const RESET_VALUE: u32 = 0x00ff_0000;
}
