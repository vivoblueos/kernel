#[doc = "Register `CFG1` reader"]
pub type R = crate::R<Cfg1Spec>;
#[doc = "Register `CFG1` writer"]
pub type W = crate::W<Cfg1Spec>;
#[doc = "Field `ADCPSC_3` reader - Bit 3 of ADCPSC"]
pub type Adcpsc3R = crate::BitReader;
#[doc = "Field `ADCPSC_3` writer - Bit 3 of ADCPSC"]
pub type Adcpsc3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLLPRESEL` reader - PLL Clock Source Selection"]
pub type PllpreselR = crate::BitReader;
#[doc = "Field `PLLPRESEL` writer - PLL Clock Source Selection"]
pub type PllpreselW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 29 - Bit 3 of ADCPSC"]
    #[inline(always)]
    pub fn adcpsc_3(&self) -> Adcpsc3R {
        Adcpsc3R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - PLL Clock Source Selection"]
    #[inline(always)]
    pub fn pllpresel(&self) -> PllpreselR {
        PllpreselR::new(((self.bits >> 30) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 29 - Bit 3 of ADCPSC"]
    #[inline(always)]
    #[must_use]
    pub fn adcpsc_3(&mut self) -> Adcpsc3W<Cfg1Spec> {
        Adcpsc3W::new(self, 29)
    }
    #[doc = "Bit 30 - PLL Clock Source Selection"]
    #[inline(always)]
    #[must_use]
    pub fn pllpresel(&mut self) -> PllpreselW<Cfg1Spec> {
        PllpreselW::new(self, 30)
    }
}
#[doc = "Clock Configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cfg1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cfg1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Cfg1Spec;
impl crate::RegisterSpec for Cfg1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cfg1::R`](R) reader structure"]
impl crate::Readable for Cfg1Spec {}
#[doc = "`write(|w| ..)` method takes [`cfg1::W`](W) writer structure"]
impl crate::Writable for Cfg1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CFG1 to value 0"]
impl crate::Resettable for Cfg1Spec {
    const RESET_VALUE: u32 = 0;
}
