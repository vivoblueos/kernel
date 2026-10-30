#[doc = "Register `CTL` reader"]
pub type R = crate::R<CtlSpec>;
#[doc = "Register `CTL` writer"]
pub type W = crate::W<CtlSpec>;
#[doc = "Field `IRC8MEN` reader - Internal 8MHz RC oscillator Enable"]
pub type Irc8menR = crate::BitReader;
#[doc = "Field `IRC8MEN` writer - Internal 8MHz RC oscillator Enable"]
pub type Irc8menW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IRC8MSTB` reader - IRC8M Internal 8MHz RC Oscillator stabilization Flag"]
pub type Irc8mstbR = crate::BitReader;
#[doc = "Field `IRC8MADJ` reader - Internal 8MHz RC Oscillator clock trim adjust value"]
pub type Irc8madjR = crate::FieldReader;
#[doc = "Field `IRC8MADJ` writer - Internal 8MHz RC Oscillator clock trim adjust value"]
pub type Irc8madjW<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `IRC8MCALIB` reader - Internal 8MHz RC Oscillator calibration value register"]
pub type Irc8mcalibR = crate::FieldReader;
#[doc = "Field `HXTALEN` reader - External High Speed oscillator Enable"]
pub type HxtalenR = crate::BitReader;
#[doc = "Field `HXTALEN` writer - External High Speed oscillator Enable"]
pub type HxtalenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HXTALSTB` reader - External crystal oscillator (HXTAL) clock stabilization flag"]
pub type HxtalstbR = crate::BitReader;
#[doc = "Field `HXTALBPS` reader - External crystal oscillator (HXTAL) clock bypass mode enable"]
pub type HxtalbpsR = crate::BitReader;
#[doc = "Field `HXTALBPS` writer - External crystal oscillator (HXTAL) clock bypass mode enable"]
pub type HxtalbpsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CKMEN` reader - HXTAL Clock Monitor Enable"]
pub type CkmenR = crate::BitReader;
#[doc = "Field `CKMEN` writer - HXTAL Clock Monitor Enable"]
pub type CkmenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLLEN` reader - PLL enable"]
pub type PllenR = crate::BitReader;
#[doc = "Field `PLLEN` writer - PLL enable"]
pub type PllenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLLSTB` reader - PLL Clock Stabilization Flag"]
pub type PllstbR = crate::BitReader;
#[doc = "Field `PLL1EN` reader - PLL1 enable"]
pub type Pll1enR = crate::BitReader;
#[doc = "Field `PLL1EN` writer - PLL1 enable"]
pub type Pll1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLL1STB` reader - PLL1 Clock Stabilization Flag"]
pub type Pll1stbR = crate::BitReader;
#[doc = "Field `PLL2EN` reader - PLL2 enable"]
pub type Pll2enR = crate::BitReader;
#[doc = "Field `PLL2EN` writer - PLL2 enable"]
pub type Pll2enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLL2STB` reader - PLL2 Clock Stabilization Flag"]
pub type Pll2stbR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Internal 8MHz RC oscillator Enable"]
    #[inline(always)]
    pub fn irc8men(&self) -> Irc8menR {
        Irc8menR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - IRC8M Internal 8MHz RC Oscillator stabilization Flag"]
    #[inline(always)]
    pub fn irc8mstb(&self) -> Irc8mstbR {
        Irc8mstbR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 3:7 - Internal 8MHz RC Oscillator clock trim adjust value"]
    #[inline(always)]
    pub fn irc8madj(&self) -> Irc8madjR {
        Irc8madjR::new(((self.bits >> 3) & 0x1f) as u8)
    }
    #[doc = "Bits 8:15 - Internal 8MHz RC Oscillator calibration value register"]
    #[inline(always)]
    pub fn irc8mcalib(&self) -> Irc8mcalibR {
        Irc8mcalibR::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bit 16 - External High Speed oscillator Enable"]
    #[inline(always)]
    pub fn hxtalen(&self) -> HxtalenR {
        HxtalenR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - External crystal oscillator (HXTAL) clock stabilization flag"]
    #[inline(always)]
    pub fn hxtalstb(&self) -> HxtalstbR {
        HxtalstbR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - External crystal oscillator (HXTAL) clock bypass mode enable"]
    #[inline(always)]
    pub fn hxtalbps(&self) -> HxtalbpsR {
        HxtalbpsR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - HXTAL Clock Monitor Enable"]
    #[inline(always)]
    pub fn ckmen(&self) -> CkmenR {
        CkmenR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 24 - PLL enable"]
    #[inline(always)]
    pub fn pllen(&self) -> PllenR {
        PllenR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - PLL Clock Stabilization Flag"]
    #[inline(always)]
    pub fn pllstb(&self) -> PllstbR {
        PllstbR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - PLL1 enable"]
    #[inline(always)]
    pub fn pll1en(&self) -> Pll1enR {
        Pll1enR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - PLL1 Clock Stabilization Flag"]
    #[inline(always)]
    pub fn pll1stb(&self) -> Pll1stbR {
        Pll1stbR::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - PLL2 enable"]
    #[inline(always)]
    pub fn pll2en(&self) -> Pll2enR {
        Pll2enR::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - PLL2 Clock Stabilization Flag"]
    #[inline(always)]
    pub fn pll2stb(&self) -> Pll2stbR {
        Pll2stbR::new(((self.bits >> 29) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Internal 8MHz RC oscillator Enable"]
    #[inline(always)]
    #[must_use]
    pub fn irc8men(&mut self) -> Irc8menW<CtlSpec> {
        Irc8menW::new(self, 0)
    }
    #[doc = "Bits 3:7 - Internal 8MHz RC Oscillator clock trim adjust value"]
    #[inline(always)]
    #[must_use]
    pub fn irc8madj(&mut self) -> Irc8madjW<CtlSpec> {
        Irc8madjW::new(self, 3)
    }
    #[doc = "Bit 16 - External High Speed oscillator Enable"]
    #[inline(always)]
    #[must_use]
    pub fn hxtalen(&mut self) -> HxtalenW<CtlSpec> {
        HxtalenW::new(self, 16)
    }
    #[doc = "Bit 18 - External crystal oscillator (HXTAL) clock bypass mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn hxtalbps(&mut self) -> HxtalbpsW<CtlSpec> {
        HxtalbpsW::new(self, 18)
    }
    #[doc = "Bit 19 - HXTAL Clock Monitor Enable"]
    #[inline(always)]
    #[must_use]
    pub fn ckmen(&mut self) -> CkmenW<CtlSpec> {
        CkmenW::new(self, 19)
    }
    #[doc = "Bit 24 - PLL enable"]
    #[inline(always)]
    #[must_use]
    pub fn pllen(&mut self) -> PllenW<CtlSpec> {
        PllenW::new(self, 24)
    }
    #[doc = "Bit 26 - PLL1 enable"]
    #[inline(always)]
    #[must_use]
    pub fn pll1en(&mut self) -> Pll1enW<CtlSpec> {
        Pll1enW::new(self, 26)
    }
    #[doc = "Bit 28 - PLL2 enable"]
    #[inline(always)]
    #[must_use]
    pub fn pll2en(&mut self) -> Pll2enW<CtlSpec> {
        Pll2enW::new(self, 28)
    }
}
#[doc = "Control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CtlSpec;
impl crate::RegisterSpec for CtlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl::R`](R) reader structure"]
impl crate::Readable for CtlSpec {}
#[doc = "`write(|w| ..)` method takes [`ctl::W`](W) writer structure"]
impl crate::Writable for CtlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL to value 0x83"]
impl crate::Resettable for CtlSpec {
    const RESET_VALUE: u32 = 0x83;
}
