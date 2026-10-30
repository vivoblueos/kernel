#[doc = "Register `CFG0` reader"]
pub type R = crate::R<Cfg0Spec>;
#[doc = "Register `CFG0` writer"]
pub type W = crate::W<Cfg0Spec>;
#[doc = "Field `SCS` reader - System clock switch"]
pub type ScsR = crate::FieldReader;
#[doc = "Field `SCS` writer - System clock switch"]
pub type ScsW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SCSS` reader - System clock switch status"]
pub type ScssR = crate::FieldReader;
#[doc = "Field `AHBPSC` reader - AHB prescaler selection"]
pub type AhbpscR = crate::FieldReader;
#[doc = "Field `AHBPSC` writer - AHB prescaler selection"]
pub type AhbpscW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `APB1PSC` reader - APB1 prescaler selection"]
pub type Apb1pscR = crate::FieldReader;
#[doc = "Field `APB1PSC` writer - APB1 prescaler selection"]
pub type Apb1pscW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `APB2PSC` reader - APB2 prescaler selection"]
pub type Apb2pscR = crate::FieldReader;
#[doc = "Field `APB2PSC` writer - APB2 prescaler selection"]
pub type Apb2pscW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `ADCPSC_1_0` reader - ADC clock prescaler selection"]
pub type Adcpsc1_0R = crate::FieldReader;
#[doc = "Field `ADCPSC_1_0` writer - ADC clock prescaler selection"]
pub type Adcpsc1_0W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PLLSEL` reader - PLL Clock Source Selection"]
pub type PllselR = crate::BitReader;
#[doc = "Field `PLLSEL` writer - PLL Clock Source Selection"]
pub type PllselW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PREDV0_LSB` reader - The LSB of PREDV0 division factor"]
pub type Predv0LsbR = crate::BitReader;
#[doc = "Field `PREDV0_LSB` writer - The LSB of PREDV0 division factor"]
pub type Predv0LsbW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLLMF_3_0` reader - The PLL clock multiplication factor"]
pub type Pllmf3_0R = crate::FieldReader;
#[doc = "Field `PLLMF_3_0` writer - The PLL clock multiplication factor"]
pub type Pllmf3_0W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `USBHSPSC_1_0` reader - USBHS clock prescaler selection"]
pub type Usbhspsc1_0R = crate::FieldReader;
#[doc = "Field `USBHSPSC_1_0` writer - USBHS clock prescaler selection"]
pub type Usbhspsc1_0W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CKOUT0SEL` reader - CKOUT0 Clock Source Selection"]
pub type Ckout0selR = crate::FieldReader;
#[doc = "Field `CKOUT0SEL` writer - CKOUT0 Clock Source Selection"]
pub type Ckout0selW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `ADCPSC_2` reader - Bit 2 of ADCPSC"]
pub type Adcpsc2R = crate::BitReader;
#[doc = "Field `ADCPSC_2` writer - Bit 2 of ADCPSC"]
pub type Adcpsc2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLLMF_5_4` reader - Bit 5 and Bit 4 of PLLMF"]
pub type Pllmf5_4R = crate::FieldReader;
#[doc = "Field `PLLMF_5_4` writer - Bit 5 and Bit 4 of PLLMF"]
pub type Pllmf5_4W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `USBHSPSC` reader - Bit 2 of USBHSPSC"]
pub type UsbhspscR = crate::BitReader;
#[doc = "Field `USBHSPSC` writer - Bit 2 of USBHSPSC"]
pub type UsbhspscW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:1 - System clock switch"]
    #[inline(always)]
    pub fn scs(&self) -> ScsR {
        ScsR::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:3 - System clock switch status"]
    #[inline(always)]
    pub fn scss(&self) -> ScssR {
        ScssR::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:7 - AHB prescaler selection"]
    #[inline(always)]
    pub fn ahbpsc(&self) -> AhbpscR {
        AhbpscR::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bits 8:10 - APB1 prescaler selection"]
    #[inline(always)]
    pub fn apb1psc(&self) -> Apb1pscR {
        Apb1pscR::new(((self.bits >> 8) & 7) as u8)
    }
    #[doc = "Bits 11:13 - APB2 prescaler selection"]
    #[inline(always)]
    pub fn apb2psc(&self) -> Apb2pscR {
        Apb2pscR::new(((self.bits >> 11) & 7) as u8)
    }
    #[doc = "Bits 14:15 - ADC clock prescaler selection"]
    #[inline(always)]
    pub fn adcpsc_1_0(&self) -> Adcpsc1_0R {
        Adcpsc1_0R::new(((self.bits >> 14) & 3) as u8)
    }
    #[doc = "Bit 16 - PLL Clock Source Selection"]
    #[inline(always)]
    pub fn pllsel(&self) -> PllselR {
        PllselR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - The LSB of PREDV0 division factor"]
    #[inline(always)]
    pub fn predv0_lsb(&self) -> Predv0LsbR {
        Predv0LsbR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bits 18:21 - The PLL clock multiplication factor"]
    #[inline(always)]
    pub fn pllmf_3_0(&self) -> Pllmf3_0R {
        Pllmf3_0R::new(((self.bits >> 18) & 0x0f) as u8)
    }
    #[doc = "Bits 22:23 - USBHS clock prescaler selection"]
    #[inline(always)]
    pub fn usbhspsc_1_0(&self) -> Usbhspsc1_0R {
        Usbhspsc1_0R::new(((self.bits >> 22) & 3) as u8)
    }
    #[doc = "Bits 24:27 - CKOUT0 Clock Source Selection"]
    #[inline(always)]
    pub fn ckout0sel(&self) -> Ckout0selR {
        Ckout0selR::new(((self.bits >> 24) & 0x0f) as u8)
    }
    #[doc = "Bit 28 - Bit 2 of ADCPSC"]
    #[inline(always)]
    pub fn adcpsc_2(&self) -> Adcpsc2R {
        Adcpsc2R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bits 29:30 - Bit 5 and Bit 4 of PLLMF"]
    #[inline(always)]
    pub fn pllmf_5_4(&self) -> Pllmf5_4R {
        Pllmf5_4R::new(((self.bits >> 29) & 3) as u8)
    }
    #[doc = "Bit 31 - Bit 2 of USBHSPSC"]
    #[inline(always)]
    pub fn usbhspsc(&self) -> UsbhspscR {
        UsbhspscR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:1 - System clock switch"]
    #[inline(always)]
    #[must_use]
    pub fn scs(&mut self) -> ScsW<Cfg0Spec> {
        ScsW::new(self, 0)
    }
    #[doc = "Bits 4:7 - AHB prescaler selection"]
    #[inline(always)]
    #[must_use]
    pub fn ahbpsc(&mut self) -> AhbpscW<Cfg0Spec> {
        AhbpscW::new(self, 4)
    }
    #[doc = "Bits 8:10 - APB1 prescaler selection"]
    #[inline(always)]
    #[must_use]
    pub fn apb1psc(&mut self) -> Apb1pscW<Cfg0Spec> {
        Apb1pscW::new(self, 8)
    }
    #[doc = "Bits 11:13 - APB2 prescaler selection"]
    #[inline(always)]
    #[must_use]
    pub fn apb2psc(&mut self) -> Apb2pscW<Cfg0Spec> {
        Apb2pscW::new(self, 11)
    }
    #[doc = "Bits 14:15 - ADC clock prescaler selection"]
    #[inline(always)]
    #[must_use]
    pub fn adcpsc_1_0(&mut self) -> Adcpsc1_0W<Cfg0Spec> {
        Adcpsc1_0W::new(self, 14)
    }
    #[doc = "Bit 16 - PLL Clock Source Selection"]
    #[inline(always)]
    #[must_use]
    pub fn pllsel(&mut self) -> PllselW<Cfg0Spec> {
        PllselW::new(self, 16)
    }
    #[doc = "Bit 17 - The LSB of PREDV0 division factor"]
    #[inline(always)]
    #[must_use]
    pub fn predv0_lsb(&mut self) -> Predv0LsbW<Cfg0Spec> {
        Predv0LsbW::new(self, 17)
    }
    #[doc = "Bits 18:21 - The PLL clock multiplication factor"]
    #[inline(always)]
    #[must_use]
    pub fn pllmf_3_0(&mut self) -> Pllmf3_0W<Cfg0Spec> {
        Pllmf3_0W::new(self, 18)
    }
    #[doc = "Bits 22:23 - USBHS clock prescaler selection"]
    #[inline(always)]
    #[must_use]
    pub fn usbhspsc_1_0(&mut self) -> Usbhspsc1_0W<Cfg0Spec> {
        Usbhspsc1_0W::new(self, 22)
    }
    #[doc = "Bits 24:27 - CKOUT0 Clock Source Selection"]
    #[inline(always)]
    #[must_use]
    pub fn ckout0sel(&mut self) -> Ckout0selW<Cfg0Spec> {
        Ckout0selW::new(self, 24)
    }
    #[doc = "Bit 28 - Bit 2 of ADCPSC"]
    #[inline(always)]
    #[must_use]
    pub fn adcpsc_2(&mut self) -> Adcpsc2W<Cfg0Spec> {
        Adcpsc2W::new(self, 28)
    }
    #[doc = "Bits 29:30 - Bit 5 and Bit 4 of PLLMF"]
    #[inline(always)]
    #[must_use]
    pub fn pllmf_5_4(&mut self) -> Pllmf5_4W<Cfg0Spec> {
        Pllmf5_4W::new(self, 29)
    }
    #[doc = "Bit 31 - Bit 2 of USBHSPSC"]
    #[inline(always)]
    #[must_use]
    pub fn usbhspsc(&mut self) -> UsbhspscW<Cfg0Spec> {
        UsbhspscW::new(self, 31)
    }
}
#[doc = "Clock configuration register 0 (RCU_CFG0)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cfg0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cfg0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Cfg0Spec;
impl crate::RegisterSpec for Cfg0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cfg0::R`](R) reader structure"]
impl crate::Readable for Cfg0Spec {}
#[doc = "`write(|w| ..)` method takes [`cfg0::W`](W) writer structure"]
impl crate::Writable for Cfg0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CFG0 to value 0"]
impl crate::Resettable for Cfg0Spec {
    const RESET_VALUE: u32 = 0;
}
