#[doc = "Register `WD2SR` reader"]
pub type R = crate::R<Wd2srSpec>;
#[doc = "Register `WD2SR` writer"]
pub type W = crate::W<Wd2srSpec>;
#[doc = "Field `AWD2CS` reader - Analog watchdog 2 channel selection"]
pub type Awd2csR = crate::FieldReader<u32>;
#[doc = "Field `AWD2CS` writer - Analog watchdog 2 channel selection"]
pub type Awd2csW<'a, REG> = crate::FieldWriter<'a, REG, 18, u32>;
impl R {
    #[doc = "Bits 0:17 - Analog watchdog 2 channel selection"]
    #[inline(always)]
    pub fn awd2cs(&self) -> Awd2csR {
        Awd2csR::new(self.bits & 0x0003_ffff)
    }
}
impl W {
    #[doc = "Bits 0:17 - Analog watchdog 2 channel selection"]
    #[inline(always)]
    #[must_use]
    pub fn awd2cs(&mut self) -> Awd2csW<Wd2srSpec> {
        Awd2csW::new(self, 0)
    }
}
#[doc = "Watchdog 2 Channel Selection Register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`wd2sr::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`wd2sr::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Wd2srSpec;
impl crate::RegisterSpec for Wd2srSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`wd2sr::R`](R) reader structure"]
impl crate::Readable for Wd2srSpec {}
#[doc = "`write(|w| ..)` method takes [`wd2sr::W`](W) writer structure"]
impl crate::Writable for Wd2srSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets WD2SR to value 0"]
impl crate::Resettable for Wd2srSpec {
    const RESET_VALUE: u32 = 0;
}
