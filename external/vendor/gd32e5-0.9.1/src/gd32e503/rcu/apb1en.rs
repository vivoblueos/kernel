#[doc = "Register `APB1EN` reader"]
pub type R = crate::R<Apb1enSpec>;
#[doc = "Register `APB1EN` writer"]
pub type W = crate::W<Apb1enSpec>;
#[doc = "Field `TIMER1EN` reader - TIMER1 timer clock enable"]
pub type Timer1enR = crate::BitReader;
#[doc = "Field `TIMER1EN` writer - TIMER1 timer clock enable"]
pub type Timer1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER2EN` reader - TIMER2 timer clock enable"]
pub type Timer2enR = crate::BitReader;
#[doc = "Field `TIMER2EN` writer - TIMER2 timer clock enable"]
pub type Timer2enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER3EN` reader - TIMER3 timer clock enable"]
pub type Timer3enR = crate::BitReader;
#[doc = "Field `TIMER3EN` writer - TIMER3 timer clock enable"]
pub type Timer3enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER4EN` reader - TIMER4 timer clock enable"]
pub type Timer4enR = crate::BitReader;
#[doc = "Field `TIMER4EN` writer - TIMER4 timer clock enable"]
pub type Timer4enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER5EN` reader - TIMER5 timer clock enable"]
pub type Timer5enR = crate::BitReader;
#[doc = "Field `TIMER5EN` writer - TIMER5 timer clock enable"]
pub type Timer5enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER6EN` reader - TIMER6 timer clock enable"]
pub type Timer6enR = crate::BitReader;
#[doc = "Field `TIMER6EN` writer - TIMER6 timer clock enable"]
pub type Timer6enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER11EN` reader - TIMER11 timer clock enable"]
pub type Timer11enR = crate::BitReader;
#[doc = "Field `TIMER11EN` writer - TIMER11 timer clock enable"]
pub type Timer11enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER12EN` reader - TIMER12 timer clock enable"]
pub type Timer12enR = crate::BitReader;
#[doc = "Field `TIMER12EN` writer - TIMER12 timer clock enable"]
pub type Timer12enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER13EN` reader - TIMER13 timer clock enable"]
pub type Timer13enR = crate::BitReader;
#[doc = "Field `TIMER13EN` writer - TIMER13 timer clock enable"]
pub type Timer13enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WWDGTEN` reader - Window watchdog timer clock enable"]
pub type WwdgtenR = crate::BitReader;
#[doc = "Field `WWDGTEN` writer - Window watchdog timer clock enable"]
pub type WwdgtenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI1EN` reader - SPI1 clock enable"]
pub type Spi1enR = crate::BitReader;
#[doc = "Field `SPI1EN` writer - SPI1 clock enable"]
pub type Spi1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI2EN` reader - SPI2 clock enable"]
pub type Spi2enR = crate::BitReader;
#[doc = "Field `SPI2EN` writer - SPI2 clock enable"]
pub type Spi2enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USART1EN` reader - USART1 clock enable"]
pub type Usart1enR = crate::BitReader;
#[doc = "Field `USART1EN` writer - USART1 clock enable"]
pub type Usart1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USART2EN` reader - USART2 clock enable"]
pub type Usart2enR = crate::BitReader;
#[doc = "Field `USART2EN` writer - USART2 clock enable"]
pub type Usart2enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UART3EN` reader - UART3 clock enable"]
pub type Uart3enR = crate::BitReader;
#[doc = "Field `UART3EN` writer - UART3 clock enable"]
pub type Uart3enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UART4EN` reader - UART4 clock enable"]
pub type Uart4enR = crate::BitReader;
#[doc = "Field `UART4EN` writer - UART4 clock enable"]
pub type Uart4enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2C0EN` reader - I2C0 clock enable"]
pub type I2c0enR = crate::BitReader;
#[doc = "Field `I2C0EN` writer - I2C0 clock enable"]
pub type I2c0enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2C1EN` reader - I2C1 clock enable"]
pub type I2c1enR = crate::BitReader;
#[doc = "Field `I2C1EN` writer - I2C1 clock enable"]
pub type I2c1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USBDEN` reader - USBD clock enable"]
pub type UsbdenR = crate::BitReader;
#[doc = "Field `USBDEN` writer - USBD clock enable"]
pub type UsbdenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2C2EN` reader - I2C2 clock enable"]
pub type I2c2enR = crate::BitReader;
#[doc = "Field `I2C2EN` writer - I2C2 clock enable"]
pub type I2c2enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAN0EN` reader - CAN0 clock enable"]
pub type Can0enR = crate::BitReader;
#[doc = "Field `CAN0EN` writer - CAN0 clock enable"]
pub type Can0enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAN1EN` reader - CAN1 clock enable"]
pub type Can1enR = crate::BitReader;
#[doc = "Field `CAN1EN` writer - CAN1 clock enable"]
pub type Can1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BKPIEN` reader - Backup interface clock enable"]
pub type BkpienR = crate::BitReader;
#[doc = "Field `BKPIEN` writer - Backup interface clock enable"]
pub type BkpienW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PMUEN` reader - Power control clock enable"]
pub type PmuenR = crate::BitReader;
#[doc = "Field `PMUEN` writer - Power control clock enable"]
pub type PmuenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DACEN` reader - DAC clock enable"]
pub type DacenR = crate::BitReader;
#[doc = "Field `DACEN` writer - DAC clock enable"]
pub type DacenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - TIMER1 timer clock enable"]
    #[inline(always)]
    pub fn timer1en(&self) -> Timer1enR {
        Timer1enR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - TIMER2 timer clock enable"]
    #[inline(always)]
    pub fn timer2en(&self) -> Timer2enR {
        Timer2enR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - TIMER3 timer clock enable"]
    #[inline(always)]
    pub fn timer3en(&self) -> Timer3enR {
        Timer3enR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - TIMER4 timer clock enable"]
    #[inline(always)]
    pub fn timer4en(&self) -> Timer4enR {
        Timer4enR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - TIMER5 timer clock enable"]
    #[inline(always)]
    pub fn timer5en(&self) -> Timer5enR {
        Timer5enR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - TIMER6 timer clock enable"]
    #[inline(always)]
    pub fn timer6en(&self) -> Timer6enR {
        Timer6enR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - TIMER11 timer clock enable"]
    #[inline(always)]
    pub fn timer11en(&self) -> Timer11enR {
        Timer11enR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - TIMER12 timer clock enable"]
    #[inline(always)]
    pub fn timer12en(&self) -> Timer12enR {
        Timer12enR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - TIMER13 timer clock enable"]
    #[inline(always)]
    pub fn timer13en(&self) -> Timer13enR {
        Timer13enR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 11 - Window watchdog timer clock enable"]
    #[inline(always)]
    pub fn wwdgten(&self) -> WwdgtenR {
        WwdgtenR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 14 - SPI1 clock enable"]
    #[inline(always)]
    pub fn spi1en(&self) -> Spi1enR {
        Spi1enR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - SPI2 clock enable"]
    #[inline(always)]
    pub fn spi2en(&self) -> Spi2enR {
        Spi2enR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 17 - USART1 clock enable"]
    #[inline(always)]
    pub fn usart1en(&self) -> Usart1enR {
        Usart1enR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - USART2 clock enable"]
    #[inline(always)]
    pub fn usart2en(&self) -> Usart2enR {
        Usart2enR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - UART3 clock enable"]
    #[inline(always)]
    pub fn uart3en(&self) -> Uart3enR {
        Uart3enR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - UART4 clock enable"]
    #[inline(always)]
    pub fn uart4en(&self) -> Uart4enR {
        Uart4enR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - I2C0 clock enable"]
    #[inline(always)]
    pub fn i2c0en(&self) -> I2c0enR {
        I2c0enR::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - I2C1 clock enable"]
    #[inline(always)]
    pub fn i2c1en(&self) -> I2c1enR {
        I2c1enR::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - USBD clock enable"]
    #[inline(always)]
    pub fn usbden(&self) -> UsbdenR {
        UsbdenR::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - I2C2 clock enable"]
    #[inline(always)]
    pub fn i2c2en(&self) -> I2c2enR {
        I2c2enR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - CAN0 clock enable"]
    #[inline(always)]
    pub fn can0en(&self) -> Can0enR {
        Can0enR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - CAN1 clock enable"]
    #[inline(always)]
    pub fn can1en(&self) -> Can1enR {
        Can1enR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - Backup interface clock enable"]
    #[inline(always)]
    pub fn bkpien(&self) -> BkpienR {
        BkpienR::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - Power control clock enable"]
    #[inline(always)]
    pub fn pmuen(&self) -> PmuenR {
        PmuenR::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - DAC clock enable"]
    #[inline(always)]
    pub fn dacen(&self) -> DacenR {
        DacenR::new(((self.bits >> 29) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - TIMER1 timer clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer1en(&mut self) -> Timer1enW<Apb1enSpec> {
        Timer1enW::new(self, 0)
    }
    #[doc = "Bit 1 - TIMER2 timer clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer2en(&mut self) -> Timer2enW<Apb1enSpec> {
        Timer2enW::new(self, 1)
    }
    #[doc = "Bit 2 - TIMER3 timer clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer3en(&mut self) -> Timer3enW<Apb1enSpec> {
        Timer3enW::new(self, 2)
    }
    #[doc = "Bit 3 - TIMER4 timer clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer4en(&mut self) -> Timer4enW<Apb1enSpec> {
        Timer4enW::new(self, 3)
    }
    #[doc = "Bit 4 - TIMER5 timer clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer5en(&mut self) -> Timer5enW<Apb1enSpec> {
        Timer5enW::new(self, 4)
    }
    #[doc = "Bit 5 - TIMER6 timer clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer6en(&mut self) -> Timer6enW<Apb1enSpec> {
        Timer6enW::new(self, 5)
    }
    #[doc = "Bit 6 - TIMER11 timer clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer11en(&mut self) -> Timer11enW<Apb1enSpec> {
        Timer11enW::new(self, 6)
    }
    #[doc = "Bit 7 - TIMER12 timer clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer12en(&mut self) -> Timer12enW<Apb1enSpec> {
        Timer12enW::new(self, 7)
    }
    #[doc = "Bit 8 - TIMER13 timer clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn timer13en(&mut self) -> Timer13enW<Apb1enSpec> {
        Timer13enW::new(self, 8)
    }
    #[doc = "Bit 11 - Window watchdog timer clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn wwdgten(&mut self) -> WwdgtenW<Apb1enSpec> {
        WwdgtenW::new(self, 11)
    }
    #[doc = "Bit 14 - SPI1 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn spi1en(&mut self) -> Spi1enW<Apb1enSpec> {
        Spi1enW::new(self, 14)
    }
    #[doc = "Bit 15 - SPI2 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn spi2en(&mut self) -> Spi2enW<Apb1enSpec> {
        Spi2enW::new(self, 15)
    }
    #[doc = "Bit 17 - USART1 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn usart1en(&mut self) -> Usart1enW<Apb1enSpec> {
        Usart1enW::new(self, 17)
    }
    #[doc = "Bit 18 - USART2 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn usart2en(&mut self) -> Usart2enW<Apb1enSpec> {
        Usart2enW::new(self, 18)
    }
    #[doc = "Bit 19 - UART3 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn uart3en(&mut self) -> Uart3enW<Apb1enSpec> {
        Uart3enW::new(self, 19)
    }
    #[doc = "Bit 20 - UART4 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn uart4en(&mut self) -> Uart4enW<Apb1enSpec> {
        Uart4enW::new(self, 20)
    }
    #[doc = "Bit 21 - I2C0 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn i2c0en(&mut self) -> I2c0enW<Apb1enSpec> {
        I2c0enW::new(self, 21)
    }
    #[doc = "Bit 22 - I2C1 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn i2c1en(&mut self) -> I2c1enW<Apb1enSpec> {
        I2c1enW::new(self, 22)
    }
    #[doc = "Bit 23 - USBD clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn usbden(&mut self) -> UsbdenW<Apb1enSpec> {
        UsbdenW::new(self, 23)
    }
    #[doc = "Bit 24 - I2C2 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn i2c2en(&mut self) -> I2c2enW<Apb1enSpec> {
        I2c2enW::new(self, 24)
    }
    #[doc = "Bit 25 - CAN0 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn can0en(&mut self) -> Can0enW<Apb1enSpec> {
        Can0enW::new(self, 25)
    }
    #[doc = "Bit 26 - CAN1 clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn can1en(&mut self) -> Can1enW<Apb1enSpec> {
        Can1enW::new(self, 26)
    }
    #[doc = "Bit 27 - Backup interface clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn bkpien(&mut self) -> BkpienW<Apb1enSpec> {
        BkpienW::new(self, 27)
    }
    #[doc = "Bit 28 - Power control clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn pmuen(&mut self) -> PmuenW<Apb1enSpec> {
        PmuenW::new(self, 28)
    }
    #[doc = "Bit 29 - DAC clock enable"]
    #[inline(always)]
    #[must_use]
    pub fn dacen(&mut self) -> DacenW<Apb1enSpec> {
        DacenW::new(self, 29)
    }
}
#[doc = "APB1 clock enable register (RCU_APB1EN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`apb1en::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`apb1en::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Apb1enSpec;
impl crate::RegisterSpec for Apb1enSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`apb1en::R`](R) reader structure"]
impl crate::Readable for Apb1enSpec {}
#[doc = "`write(|w| ..)` method takes [`apb1en::W`](W) writer structure"]
impl crate::Writable for Apb1enSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets APB1EN to value 0"]
impl crate::Resettable for Apb1enSpec {
    const RESET_VALUE: u32 = 0;
}
