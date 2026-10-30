#[doc = "Register `CFG1` reader"]
pub type R = crate::R<Cfg1Spec>;
#[doc = "Register `CFG1` writer"]
pub type W = crate::W<Cfg1Spec>;
#[doc = "Field `PREDV0` reader - PREDV0 division factor"]
pub type Predv0R = crate::FieldReader;
#[doc = "Field `PREDV0` writer - PREDV0 division factor"]
pub type Predv0W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `PREDV1` reader - PREDV1 division factor"]
pub type Predv1R = crate::FieldReader;
#[doc = "Field `PREDV1` writer - PREDV1 division factor"]
pub type Predv1W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `PLL1MF` reader - The PLL1 clock multiplication factor"]
pub type Pll1mfR = crate::FieldReader;
#[doc = "Field `PLL1MF` writer - The PLL1 clock multiplication factor"]
pub type Pll1mfW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `PLL2MF` reader - The PLL2 clock multiplication factor"]
pub type Pll2mfR = crate::FieldReader;
#[doc = "Field `PLL2MF` writer - The PLL2 clock multiplication factor"]
pub type Pll2mfW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `PREDV0SEL` reader - PREDV0 input Clock Source Selection"]
pub type Predv0selR = crate::BitReader;
#[doc = "Field `PREDV0SEL` writer - PREDV0 input Clock Source Selection"]
pub type Predv0selW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2S1SEL` reader - I2S1 Clock Source Selection"]
pub type I2s1selR = crate::BitReader;
#[doc = "Field `I2S1SEL` writer - I2S1 Clock Source Selection"]
pub type I2s1selW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2S2SEL` reader - I2S2 Clock Source Selection"]
pub type I2s2selR = crate::BitReader;
#[doc = "Field `I2S2SEL` writer - I2S2 Clock Source Selection"]
pub type I2s2selW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SHRTIMERSEL` reader - SHRTIMER Clock Source Selection"]
pub type ShrtimerselR = crate::BitReader;
#[doc = "Field `SHRTIMERSEL` writer - SHRTIMER Clock Source Selection"]
pub type ShrtimerselW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLL2MF_5` reader - Bit 5 of PLL2MF"]
pub type Pll2mf5R = crate::BitReader;
#[doc = "Field `PLL2MF_5` writer - Bit 5 of PLL2MF"]
pub type Pll2mf5W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADCPSC_3` reader - Bit 3 of ADCPSC"]
pub type Adcpsc3R = crate::BitReader;
#[doc = "Field `ADCPSC_3` writer - Bit 3 of ADCPSC"]
pub type Adcpsc3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLLPRESEL` reader - PLL Clock Source Selection"]
pub type PllpreselR = crate::BitReader;
#[doc = "Field `PLLPRESEL` writer - PLL Clock Source Selection"]
pub type PllpreselW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLL2MF_4` reader - Bit 4 of PLL2MF"]
pub type Pll2mf4R = crate::BitReader;
#[doc = "Field `PLL2MF_4` writer - Bit 4 of PLL2MF"]
pub type Pll2mf4W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:3 - PREDV0 division factor"]
    #[inline(always)]
    pub fn predv0(&self) -> Predv0R {
        Predv0R::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:7 - PREDV1 division factor"]
    #[inline(always)]
    pub fn predv1(&self) -> Predv1R {
        Predv1R::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bits 8:11 - The PLL1 clock multiplication factor"]
    #[inline(always)]
    pub fn pll1mf(&self) -> Pll1mfR {
        Pll1mfR::new(((self.bits >> 8) & 0x0f) as u8)
    }
    #[doc = "Bits 12:15 - The PLL2 clock multiplication factor"]
    #[inline(always)]
    pub fn pll2mf(&self) -> Pll2mfR {
        Pll2mfR::new(((self.bits >> 12) & 0x0f) as u8)
    }
    #[doc = "Bit 16 - PREDV0 input Clock Source Selection"]
    #[inline(always)]
    pub fn predv0sel(&self) -> Predv0selR {
        Predv0selR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - I2S1 Clock Source Selection"]
    #[inline(always)]
    pub fn i2s1sel(&self) -> I2s1selR {
        I2s1selR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - I2S2 Clock Source Selection"]
    #[inline(always)]
    pub fn i2s2sel(&self) -> I2s2selR {
        I2s2selR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - SHRTIMER Clock Source Selection"]
    #[inline(always)]
    pub fn shrtimersel(&self) -> ShrtimerselR {
        ShrtimerselR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 28 - Bit 5 of PLL2MF"]
    #[inline(always)]
    pub fn pll2mf_5(&self) -> Pll2mf5R {
        Pll2mf5R::new(((self.bits >> 28) & 1) != 0)
    }
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
    #[doc = "Bit 31 - Bit 4 of PLL2MF"]
    #[inline(always)]
    pub fn pll2mf_4(&self) -> Pll2mf4R {
        Pll2mf4R::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:3 - PREDV0 division factor"]
    #[inline(always)]
    #[must_use]
    pub fn predv0(&mut self) -> Predv0W<Cfg1Spec> {
        Predv0W::new(self, 0)
    }
    #[doc = "Bits 4:7 - PREDV1 division factor"]
    #[inline(always)]
    #[must_use]
    pub fn predv1(&mut self) -> Predv1W<Cfg1Spec> {
        Predv1W::new(self, 4)
    }
    #[doc = "Bits 8:11 - The PLL1 clock multiplication factor"]
    #[inline(always)]
    #[must_use]
    pub fn pll1mf(&mut self) -> Pll1mfW<Cfg1Spec> {
        Pll1mfW::new(self, 8)
    }
    #[doc = "Bits 12:15 - The PLL2 clock multiplication factor"]
    #[inline(always)]
    #[must_use]
    pub fn pll2mf(&mut self) -> Pll2mfW<Cfg1Spec> {
        Pll2mfW::new(self, 12)
    }
    #[doc = "Bit 16 - PREDV0 input Clock Source Selection"]
    #[inline(always)]
    #[must_use]
    pub fn predv0sel(&mut self) -> Predv0selW<Cfg1Spec> {
        Predv0selW::new(self, 16)
    }
    #[doc = "Bit 17 - I2S1 Clock Source Selection"]
    #[inline(always)]
    #[must_use]
    pub fn i2s1sel(&mut self) -> I2s1selW<Cfg1Spec> {
        I2s1selW::new(self, 17)
    }
    #[doc = "Bit 18 - I2S2 Clock Source Selection"]
    #[inline(always)]
    #[must_use]
    pub fn i2s2sel(&mut self) -> I2s2selW<Cfg1Spec> {
        I2s2selW::new(self, 18)
    }
    #[doc = "Bit 19 - SHRTIMER Clock Source Selection"]
    #[inline(always)]
    #[must_use]
    pub fn shrtimersel(&mut self) -> ShrtimerselW<Cfg1Spec> {
        ShrtimerselW::new(self, 19)
    }
    #[doc = "Bit 28 - Bit 5 of PLL2MF"]
    #[inline(always)]
    #[must_use]
    pub fn pll2mf_5(&mut self) -> Pll2mf5W<Cfg1Spec> {
        Pll2mf5W::new(self, 28)
    }
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
    #[doc = "Bit 31 - Bit 4 of PLL2MF"]
    #[inline(always)]
    #[must_use]
    pub fn pll2mf_4(&mut self) -> Pll2mf4W<Cfg1Spec> {
        Pll2mf4W::new(self, 31)
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
