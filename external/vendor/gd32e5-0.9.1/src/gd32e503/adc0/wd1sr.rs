#[doc = "Register `WD1SR` reader"]
pub type R = crate::R<Wd1srSpec>;
#[doc = "Register `WD1SR` writer"]
pub type W = crate::W<Wd1srSpec>;
#[doc = "Field `AWD1CS` reader - Analog watchdog 1 channel selection"]
pub type Awd1csR = crate::FieldReader<u32>;
#[doc = "Field `AWD1CS` writer - Analog watchdog 1 channel selection"]
pub type Awd1csW<'a, REG> = crate::FieldWriter<'a, REG, 18, u32>;
impl R {
    #[doc = "Bits 0:17 - Analog watchdog 1 channel selection"]
    #[inline(always)]
    pub fn awd1cs(&self) -> Awd1csR {
        Awd1csR::new(self.bits & 0x0003_ffff)
    }
}
impl W {
    #[doc = "Bits 0:17 - Analog watchdog 1 channel selection"]
    #[inline(always)]
    #[must_use]
    pub fn awd1cs(&mut self) -> Awd1csW<Wd1srSpec> {
        Awd1csW::new(self, 0)
    }
}
#[doc = "Watchdog 1 Channel Selection Register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`wd1sr::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`wd1sr::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Wd1srSpec;
impl crate::RegisterSpec for Wd1srSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`wd1sr::R`](R) reader structure"]
impl crate::Readable for Wd1srSpec {}
#[doc = "`write(|w| ..)` method takes [`wd1sr::W`](W) writer structure"]
impl crate::Writable for Wd1srSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets WD1SR to value 0"]
impl crate::Resettable for Wd1srSpec {
    const RESET_VALUE: u32 = 0;
}
