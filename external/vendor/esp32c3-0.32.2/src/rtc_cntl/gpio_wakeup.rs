#[doc = "Register `GPIO_WAKEUP` reader"]
pub type R = crate::R<GPIO_WAKEUP_SPEC>;
#[doc = "Register `GPIO_WAKEUP` writer"]
pub type W = crate::W<GPIO_WAKEUP_SPEC>;
#[doc = "Field `GPIO_WAKEUP_STATUS` reader - rtc gpio wakeup flag"]
pub type GPIO_WAKEUP_STATUS_R = crate::FieldReader;
#[doc = "Field `GPIO_WAKEUP_STATUS_CLR` reader - clear rtc gpio wakeup flag"]
pub type GPIO_WAKEUP_STATUS_CLR_R = crate::BitReader;
#[doc = "Field `GPIO_WAKEUP_STATUS_CLR` writer - clear rtc gpio wakeup flag"]
pub type GPIO_WAKEUP_STATUS_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_PIN_CLK_GATE` reader - enable rtc io clk gate"]
pub type GPIO_PIN_CLK_GATE_R = crate::BitReader;
#[doc = "Field `GPIO_PIN_CLK_GATE` writer - enable rtc io clk gate"]
pub type GPIO_PIN_CLK_GATE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_PIN5_INT_TYPE` reader - configure gpio wakeup type"]
pub type GPIO_PIN5_INT_TYPE_R = crate::FieldReader;
#[doc = "Field `GPIO_PIN5_INT_TYPE` writer - configure gpio wakeup type"]
pub type GPIO_PIN5_INT_TYPE_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `GPIO_PIN4_INT_TYPE` reader - configure gpio wakeup type"]
pub type GPIO_PIN4_INT_TYPE_R = crate::FieldReader;
#[doc = "Field `GPIO_PIN4_INT_TYPE` writer - configure gpio wakeup type"]
pub type GPIO_PIN4_INT_TYPE_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `GPIO_PIN3_INT_TYPE` reader - configure gpio wakeup type"]
pub type GPIO_PIN3_INT_TYPE_R = crate::FieldReader;
#[doc = "Field `GPIO_PIN3_INT_TYPE` writer - configure gpio wakeup type"]
pub type GPIO_PIN3_INT_TYPE_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `GPIO_PIN2_INT_TYPE` reader - configure gpio wakeup type"]
pub type GPIO_PIN2_INT_TYPE_R = crate::FieldReader;
#[doc = "Field `GPIO_PIN2_INT_TYPE` writer - configure gpio wakeup type"]
pub type GPIO_PIN2_INT_TYPE_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `GPIO_PIN1_INT_TYPE` reader - configure gpio wakeup type"]
pub type GPIO_PIN1_INT_TYPE_R = crate::FieldReader;
#[doc = "Field `GPIO_PIN1_INT_TYPE` writer - configure gpio wakeup type"]
pub type GPIO_PIN1_INT_TYPE_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `GPIO_PIN0_INT_TYPE` reader - configure gpio wakeup type"]
pub type GPIO_PIN0_INT_TYPE_R = crate::FieldReader;
#[doc = "Field `GPIO_PIN0_INT_TYPE` writer - configure gpio wakeup type"]
pub type GPIO_PIN0_INT_TYPE_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `GPIO_PIN5_WAKEUP_ENABLE` reader - enable wakeup from rtc gpio5"]
pub type GPIO_PIN5_WAKEUP_ENABLE_R = crate::BitReader;
#[doc = "Field `GPIO_PIN5_WAKEUP_ENABLE` writer - enable wakeup from rtc gpio5"]
pub type GPIO_PIN5_WAKEUP_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_PIN4_WAKEUP_ENABLE` reader - enable wakeup from rtc gpio4"]
pub type GPIO_PIN4_WAKEUP_ENABLE_R = crate::BitReader;
#[doc = "Field `GPIO_PIN4_WAKEUP_ENABLE` writer - enable wakeup from rtc gpio4"]
pub type GPIO_PIN4_WAKEUP_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_PIN3_WAKEUP_ENABLE` reader - enable wakeup from rtc gpio3"]
pub type GPIO_PIN3_WAKEUP_ENABLE_R = crate::BitReader;
#[doc = "Field `GPIO_PIN3_WAKEUP_ENABLE` writer - enable wakeup from rtc gpio3"]
pub type GPIO_PIN3_WAKEUP_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_PIN2_WAKEUP_ENABLE` reader - enable wakeup from rtc gpio2"]
pub type GPIO_PIN2_WAKEUP_ENABLE_R = crate::BitReader;
#[doc = "Field `GPIO_PIN2_WAKEUP_ENABLE` writer - enable wakeup from rtc gpio2"]
pub type GPIO_PIN2_WAKEUP_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_PIN1_WAKEUP_ENABLE` reader - enable wakeup from rtc gpio1"]
pub type GPIO_PIN1_WAKEUP_ENABLE_R = crate::BitReader;
#[doc = "Field `GPIO_PIN1_WAKEUP_ENABLE` writer - enable wakeup from rtc gpio1"]
pub type GPIO_PIN1_WAKEUP_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_PIN0_WAKEUP_ENABLE` reader - enable wakeup from rtc gpio0"]
pub type GPIO_PIN0_WAKEUP_ENABLE_R = crate::BitReader;
#[doc = "Field `GPIO_PIN0_WAKEUP_ENABLE` writer - enable wakeup from rtc gpio0"]
pub type GPIO_PIN0_WAKEUP_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:5 - rtc gpio wakeup flag"]
    #[inline(always)]
    pub fn gpio_wakeup_status(&self) -> GPIO_WAKEUP_STATUS_R {
        GPIO_WAKEUP_STATUS_R::new((self.bits & 0x3f) as u8)
    }
    #[doc = "Bit 6 - clear rtc gpio wakeup flag"]
    #[inline(always)]
    pub fn gpio_wakeup_status_clr(&self) -> GPIO_WAKEUP_STATUS_CLR_R {
        GPIO_WAKEUP_STATUS_CLR_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - enable rtc io clk gate"]
    #[inline(always)]
    pub fn gpio_pin_clk_gate(&self) -> GPIO_PIN_CLK_GATE_R {
        GPIO_PIN_CLK_GATE_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:10 - configure gpio wakeup type"]
    #[inline(always)]
    pub fn gpio_pin5_int_type(&self) -> GPIO_PIN5_INT_TYPE_R {
        GPIO_PIN5_INT_TYPE_R::new(((self.bits >> 8) & 7) as u8)
    }
    #[doc = "Bits 11:13 - configure gpio wakeup type"]
    #[inline(always)]
    pub fn gpio_pin4_int_type(&self) -> GPIO_PIN4_INT_TYPE_R {
        GPIO_PIN4_INT_TYPE_R::new(((self.bits >> 11) & 7) as u8)
    }
    #[doc = "Bits 14:16 - configure gpio wakeup type"]
    #[inline(always)]
    pub fn gpio_pin3_int_type(&self) -> GPIO_PIN3_INT_TYPE_R {
        GPIO_PIN3_INT_TYPE_R::new(((self.bits >> 14) & 7) as u8)
    }
    #[doc = "Bits 17:19 - configure gpio wakeup type"]
    #[inline(always)]
    pub fn gpio_pin2_int_type(&self) -> GPIO_PIN2_INT_TYPE_R {
        GPIO_PIN2_INT_TYPE_R::new(((self.bits >> 17) & 7) as u8)
    }
    #[doc = "Bits 20:22 - configure gpio wakeup type"]
    #[inline(always)]
    pub fn gpio_pin1_int_type(&self) -> GPIO_PIN1_INT_TYPE_R {
        GPIO_PIN1_INT_TYPE_R::new(((self.bits >> 20) & 7) as u8)
    }
    #[doc = "Bits 23:25 - configure gpio wakeup type"]
    #[inline(always)]
    pub fn gpio_pin0_int_type(&self) -> GPIO_PIN0_INT_TYPE_R {
        GPIO_PIN0_INT_TYPE_R::new(((self.bits >> 23) & 7) as u8)
    }
    #[doc = "Bit 26 - enable wakeup from rtc gpio5"]
    #[inline(always)]
    pub fn gpio_pin5_wakeup_enable(&self) -> GPIO_PIN5_WAKEUP_ENABLE_R {
        GPIO_PIN5_WAKEUP_ENABLE_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - enable wakeup from rtc gpio4"]
    #[inline(always)]
    pub fn gpio_pin4_wakeup_enable(&self) -> GPIO_PIN4_WAKEUP_ENABLE_R {
        GPIO_PIN4_WAKEUP_ENABLE_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - enable wakeup from rtc gpio3"]
    #[inline(always)]
    pub fn gpio_pin3_wakeup_enable(&self) -> GPIO_PIN3_WAKEUP_ENABLE_R {
        GPIO_PIN3_WAKEUP_ENABLE_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - enable wakeup from rtc gpio2"]
    #[inline(always)]
    pub fn gpio_pin2_wakeup_enable(&self) -> GPIO_PIN2_WAKEUP_ENABLE_R {
        GPIO_PIN2_WAKEUP_ENABLE_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - enable wakeup from rtc gpio1"]
    #[inline(always)]
    pub fn gpio_pin1_wakeup_enable(&self) -> GPIO_PIN1_WAKEUP_ENABLE_R {
        GPIO_PIN1_WAKEUP_ENABLE_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - enable wakeup from rtc gpio0"]
    #[inline(always)]
    pub fn gpio_pin0_wakeup_enable(&self) -> GPIO_PIN0_WAKEUP_ENABLE_R {
        GPIO_PIN0_WAKEUP_ENABLE_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("GPIO_WAKEUP")
            .field("gpio_wakeup_status", &self.gpio_wakeup_status())
            .field("gpio_wakeup_status_clr", &self.gpio_wakeup_status_clr())
            .field("gpio_pin_clk_gate", &self.gpio_pin_clk_gate())
            .field("gpio_pin5_int_type", &self.gpio_pin5_int_type())
            .field("gpio_pin4_int_type", &self.gpio_pin4_int_type())
            .field("gpio_pin3_int_type", &self.gpio_pin3_int_type())
            .field("gpio_pin2_int_type", &self.gpio_pin2_int_type())
            .field("gpio_pin1_int_type", &self.gpio_pin1_int_type())
            .field("gpio_pin0_int_type", &self.gpio_pin0_int_type())
            .field("gpio_pin5_wakeup_enable", &self.gpio_pin5_wakeup_enable())
            .field("gpio_pin4_wakeup_enable", &self.gpio_pin4_wakeup_enable())
            .field("gpio_pin3_wakeup_enable", &self.gpio_pin3_wakeup_enable())
            .field("gpio_pin2_wakeup_enable", &self.gpio_pin2_wakeup_enable())
            .field("gpio_pin1_wakeup_enable", &self.gpio_pin1_wakeup_enable())
            .field("gpio_pin0_wakeup_enable", &self.gpio_pin0_wakeup_enable())
            .finish()
    }
}
impl W {
    #[doc = "Bit 6 - clear rtc gpio wakeup flag"]
    #[inline(always)]
    pub fn gpio_wakeup_status_clr(&mut self) -> GPIO_WAKEUP_STATUS_CLR_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_WAKEUP_STATUS_CLR_W::new(self, 6)
    }
    #[doc = "Bit 7 - enable rtc io clk gate"]
    #[inline(always)]
    pub fn gpio_pin_clk_gate(&mut self) -> GPIO_PIN_CLK_GATE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN_CLK_GATE_W::new(self, 7)
    }
    #[doc = "Bits 8:10 - configure gpio wakeup type"]
    #[inline(always)]
    pub fn gpio_pin5_int_type(&mut self) -> GPIO_PIN5_INT_TYPE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN5_INT_TYPE_W::new(self, 8)
    }
    #[doc = "Bits 11:13 - configure gpio wakeup type"]
    #[inline(always)]
    pub fn gpio_pin4_int_type(&mut self) -> GPIO_PIN4_INT_TYPE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN4_INT_TYPE_W::new(self, 11)
    }
    #[doc = "Bits 14:16 - configure gpio wakeup type"]
    #[inline(always)]
    pub fn gpio_pin3_int_type(&mut self) -> GPIO_PIN3_INT_TYPE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN3_INT_TYPE_W::new(self, 14)
    }
    #[doc = "Bits 17:19 - configure gpio wakeup type"]
    #[inline(always)]
    pub fn gpio_pin2_int_type(&mut self) -> GPIO_PIN2_INT_TYPE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN2_INT_TYPE_W::new(self, 17)
    }
    #[doc = "Bits 20:22 - configure gpio wakeup type"]
    #[inline(always)]
    pub fn gpio_pin1_int_type(&mut self) -> GPIO_PIN1_INT_TYPE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN1_INT_TYPE_W::new(self, 20)
    }
    #[doc = "Bits 23:25 - configure gpio wakeup type"]
    #[inline(always)]
    pub fn gpio_pin0_int_type(&mut self) -> GPIO_PIN0_INT_TYPE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN0_INT_TYPE_W::new(self, 23)
    }
    #[doc = "Bit 26 - enable wakeup from rtc gpio5"]
    #[inline(always)]
    pub fn gpio_pin5_wakeup_enable(&mut self) -> GPIO_PIN5_WAKEUP_ENABLE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN5_WAKEUP_ENABLE_W::new(self, 26)
    }
    #[doc = "Bit 27 - enable wakeup from rtc gpio4"]
    #[inline(always)]
    pub fn gpio_pin4_wakeup_enable(&mut self) -> GPIO_PIN4_WAKEUP_ENABLE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN4_WAKEUP_ENABLE_W::new(self, 27)
    }
    #[doc = "Bit 28 - enable wakeup from rtc gpio3"]
    #[inline(always)]
    pub fn gpio_pin3_wakeup_enable(&mut self) -> GPIO_PIN3_WAKEUP_ENABLE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN3_WAKEUP_ENABLE_W::new(self, 28)
    }
    #[doc = "Bit 29 - enable wakeup from rtc gpio2"]
    #[inline(always)]
    pub fn gpio_pin2_wakeup_enable(&mut self) -> GPIO_PIN2_WAKEUP_ENABLE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN2_WAKEUP_ENABLE_W::new(self, 29)
    }
    #[doc = "Bit 30 - enable wakeup from rtc gpio1"]
    #[inline(always)]
    pub fn gpio_pin1_wakeup_enable(&mut self) -> GPIO_PIN1_WAKEUP_ENABLE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN1_WAKEUP_ENABLE_W::new(self, 30)
    }
    #[doc = "Bit 31 - enable wakeup from rtc gpio0"]
    #[inline(always)]
    pub fn gpio_pin0_wakeup_enable(&mut self) -> GPIO_PIN0_WAKEUP_ENABLE_W<'_, GPIO_WAKEUP_SPEC> {
        GPIO_PIN0_WAKEUP_ENABLE_W::new(self, 31)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`gpio_wakeup::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`gpio_wakeup::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GPIO_WAKEUP_SPEC;
impl crate::RegisterSpec for GPIO_WAKEUP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`gpio_wakeup::R`](R) reader structure"]
impl crate::Readable for GPIO_WAKEUP_SPEC {}
#[doc = "`write(|w| ..)` method takes [`gpio_wakeup::W`](W) writer structure"]
impl crate::Writable for GPIO_WAKEUP_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets GPIO_WAKEUP to value 0"]
impl crate::Resettable for GPIO_WAKEUP_SPEC {}
