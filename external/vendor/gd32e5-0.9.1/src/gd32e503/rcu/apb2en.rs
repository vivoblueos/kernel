#[doc = "Register `APB2EN` reader"]
pub type R = crate::R<Apb2enSpec>;
#[doc = "Register `APB2EN` writer"]
pub type W = crate::W<Apb2enSpec>;
#[doc = "Field `AFEN` reader - Alternate function IO clock enable"]
pub type AfenR = crate::BitReader;
#[doc = "Field `AFEN` writer - Alternate function IO clock enable"]
pub type AfenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PAEN` reader - GPIO port A clock enable"]
pub type PaenR = crate::BitReader;
#[doc = "Field `PAEN` writer - GPIO port A clock enable"]
pub type PaenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PBEN` reader - GPIO port B clock enable"]
pub type PbenR = crate::BitReader;
#[doc = "Field `PBEN` writer - GPIO port B clock enable"]
pub type PbenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PCEN` reader - GPIO port C clock enable"]
pub type PcenR = crate::BitReader;
#[doc = "Field `PCEN` writer - GPIO port C clock enable"]
pub type PcenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PDEN` reader - GPIO port D clock enable"]
pub type PdenR = crate::BitReader;
#[doc = "Field `PDEN` writer - GPIO port D clock enable"]
pub type PdenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PEEN` reader - GPIO port E clock enable"]
pub type PeenR = crate::BitReader;
#[doc = "Field `PEEN` writer - GPIO port E clock enable"]
pub type PeenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PFEN` reader - GPIO port F clock enable"]
pub type PfenR = crate::BitReader;
#[doc = "Field `PFEN` writer - GPIO port F clock enable"]
pub type PfenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PGEN` reader - GPIO port G clock enable"]
pub type PgenR = crate::BitReader;
#[doc = "Field `PGEN` writer - GPIO port G clock enable"]
pub type PgenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADC0EN` reader - ADC0 clock enable"]
pub type Adc0enR = crate::BitReader;
#[doc = "Field `ADC0EN` writer - ADC0 clock enable"]
pub type Adc0enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADC1EN` reader - ADC1 clock enable"]
pub type Adc1enR = crate::BitReader;
#[doc = "Field `ADC1EN` writer - ADC1 clock enable"]
pub type Adc1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER0EN` reader - TIMER0 clock enable"]
pub type Timer0enR = crate::BitReader;
#[doc = "Field `TIMER0EN` writer - TIMER0 clock enable"]
pub type Timer0enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI0EN` reader - SPI0 clock enable"]
pub type Spi0enR = crate::BitReader;
#[doc = "Field `SPI0EN` writer - SPI0 clock enable"]
pub type Spi0enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER7EN` reader - TIMER7 clock enable"]
pub type Timer7enR = crate::BitReader;
#[doc = "Field `TIMER7EN` writer - TIMER7 clock enable"]
pub type Timer7enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USART0EN` reader - USART0 clock enable"]
pub type Usart0enR = crate::BitReader;
#[doc = "Field `USART0EN` writer - USART0 clock enable"]
pub type Usart0enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADC2EN` reader - ADC2 clock enable"]
pub type Adc2enR = crate::BitReader;
#[doc = "Field `ADC2EN` writer - ADC2 clock enable"]
pub type Adc2enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER8EN` reader - TIMER8 clock enable"]
pub type Timer8enR = crate::BitReader;
#[doc = "Field `TIMER8EN` writer - TIMER8 clock enable"]
pub type Timer8enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER9EN` reader - TIMER9 clock enable"]
pub type Timer9enR = crate::BitReader;
#[doc = "Field `TIMER9EN` writer - TIMER9 clock enable"]
pub type Timer9enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER10EN` reader - TIMER10 clock enable"]
pub type Timer10enR = crate::BitReader;
#[doc = "Field `TIMER10EN` writer - TIMER10 clock enable"]
pub type Timer10enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USART5EN` reader - USART5 clock enable"]
pub type Usart5enR = crate::BitReader;
#[doc = "Field `USART5EN` writer - USART5 clock enable"]
pub type Usart5enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SHRTIMEREN` reader - SHRTIMER clock enable"]
pub type ShrtimerenR = crate::BitReader;
#[doc = "Field `SHRTIMEREN` writer - SHRTIMER clock enable"]
pub type ShrtimerenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Alternate function IO clock enable"]
    #[inline(always)]
    pub fn afen(&self) -> AfenR {
        AfenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 2 - GPIO port A clock enable"]
    #[inline(always)]
    pub fn paen(&self) -> PaenR {
        PaenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - GPIO port B clock enable"]
    #[inline(always)]
    pub fn pben(&self) -> PbenR {
        PbenR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - GPIO port C clock enable"]
    #[inline(always)]
    pub fn pcen(&self) -> PcenR {
        PcenR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - GPIO port D clock enable"]
    #[inline(always)]
    pub fn pden(&self) -> PdenR {
        PdenR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - GPIO port E clock enable"]
    #[inline(always)]
    pub fn peen(&self) -> PeenR {
        PeenR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - GPIO port F clock enable"]
    #[inline(always)]
    pub fn pfen(&self) -> PfenR {
        PfenR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - GPIO port G clock enable"]
    #[inline(always)]
    pub fn pgen(&self) -> PgenR {
        PgenR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - ADC0 clock enable"]
    #[inline(always)]
    pub fn adc0en(&self) -> Adc0enR {
        Adc0enR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - ADC1 clock enable"]
    #[inline(always)]
    pub fn adc1en(&self) -> Adc1enR {
        Adc1enR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - TIMER0 clock enable"]
    #[inline(always)]
    pub fn timer0en(&self) -> Timer0enR {
        Timer0enR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - SPI0 clock enable"]
    #[inline(always)]
    pub fn spi0en(&self) -> Spi0enR {
        Spi0enR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - TIMER7 clock enable"]
    #[inline(always)]
    pub fn timer7en(&self) -> Timer7enR {
        Timer7enR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - USART0 clock enable"]
    #[inline(always)]
    pub fn usart0en(&self) -> Usart0enR {
        Usart0enR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - ADC2 clock enable"]
    #[inline(always)]
    pub fn adc2en(&self) -> Adc2enR {
        Adc2enR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 19 - TIMER8 clock enable"]
    #[inline(always)]
    pub fn timer8en(&self) -> Timer8enR {
        Timer8enR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - TIMER9 clock enable"]
    #[inline(always)]
    pub fn timer9en(&self) -> Timer9enR {
        Timer9enR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - TIMER10 clock enable"]
    #[inline(always)]
    pub fn timer10en(&self) -> Timer10enR {
        Timer10enR::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 28 - USART5 clock enable"]
    #[inline(always)]
    pub fn usart5en(&self) -> Usart5enR {
        Usart5enR::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - SHRTIMER clock enable"]
    #[inline(always)]
    pub fn shrtimeren(&self) -> ShrtimerenR {
        ShrtimerenR::new(((self.bits >> 29) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Alternate function IO clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn afen(&mut self) -> AfenW<Apb2enSpec> {
        AfenW::new(self, 0)
    }
    #[doc = "Bit 2 - GPIO port A clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn paen(&mut self) -> PaenW<Apb2enSpec> {
        PaenW::new(self, 2)
    }
    #[doc = "Bit 3 - GPIO port B clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn pben(&mut self) -> PbenW<Apb2enSpec> {
        PbenW::new(self, 3)
    }
    #[doc = "Bit 4 - GPIO port C clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn pcen(&mut self) -> PcenW<Apb2enSpec> {
        PcenW::new(self, 4)
    }
    #[doc = "Bit 5 - GPIO port D clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn pden(&mut self) -> PdenW<Apb2enSpec> {
        PdenW::new(self, 5)
    }
    #[doc = "Bit 6 - GPIO port E clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn peen(&mut self) -> PeenW<Apb2enSpec> {
        PeenW::new(self, 6)
    }
    #[doc = "Bit 7 - GPIO port F clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn pfen(&mut self) -> PfenW<Apb2enSpec> {
        PfenW::new(self, 7)
    }
    #[doc = "Bit 8 - GPIO port G clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn pgen(&mut self) -> PgenW<Apb2enSpec> {
        PgenW::new(self, 8)
    }
    #[doc = "Bit 9 - ADC0 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn adc0en(&mut self) -> Adc0enW<Apb2enSpec> {
        Adc0enW::new(self, 9)
    }
    #[doc = "Bit 10 - ADC1 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn adc1en(&mut self) -> Adc1enW<Apb2enSpec> {
        Adc1enW::new(self, 10)
    }
    #[doc = "Bit 11 - TIMER0 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer0en(&mut self) -> Timer0enW<Apb2enSpec> {
        Timer0enW::new(self, 11)
    }
    #[doc = "Bit 12 - SPI0 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn spi0en(&mut self) -> Spi0enW<Apb2enSpec> {
        Spi0enW::new(self, 12)
    }
    #[doc = "Bit 13 - TIMER7 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer7en(&mut self) -> Timer7enW<Apb2enSpec> {
        Timer7enW::new(self, 13)
    }
    #[doc = "Bit 14 - USART0 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn usart0en(&mut self) -> Usart0enW<Apb2enSpec> {
        Usart0enW::new(self, 14)
    }
    #[doc = "Bit 15 - ADC2 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn adc2en(&mut self) -> Adc2enW<Apb2enSpec> {
        Adc2enW::new(self, 15)
    }
    #[doc = "Bit 19 - TIMER8 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer8en(&mut self) -> Timer8enW<Apb2enSpec> {
        Timer8enW::new(self, 19)
    }
    #[doc = "Bit 20 - TIMER9 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer9en(&mut self) -> Timer9enW<Apb2enSpec> {
        Timer9enW::new(self, 20)
    }
    #[doc = "Bit 21 - TIMER10 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer10en(&mut self) -> Timer10enW<Apb2enSpec> {
        Timer10enW::new(self, 21)
    }
    #[doc = "Bit 28 - USART5 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn usart5en(&mut self) -> Usart5enW<Apb2enSpec> {
        Usart5enW::new(self, 28)
    }
    #[doc = "Bit 29 - SHRTIMER clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn shrtimeren(&mut self) -> ShrtimerenW<Apb2enSpec> {
        ShrtimerenW::new(self, 29)
    }
}
#[doc = "APB2 clock enable register (RCU_APB2EN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`apb2en::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`apb2en::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Apb2enSpec;
impl crate::RegisterSpec for Apb2enSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`apb2en::R`](R) reader structure"]
impl crate::Readable for Apb2enSpec {}
#[doc = "`write(|w| ..)` method takes [`apb2en::W`](W) writer structure"]
impl crate::Writable for Apb2enSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets APB2EN to value 0"]
impl crate::Resettable for Apb2enSpec {
    const RESET_VALUE: u32 = 0;
}
