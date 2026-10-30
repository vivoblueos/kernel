#[doc = "Register `PAD_HOLD` reader"]
pub type R = crate::R<PAD_HOLD_SPEC>;
#[doc = "Register `PAD_HOLD` writer"]
pub type W = crate::W<PAD_HOLD_SPEC>;
#[doc = "Field `GPIO_PIN0_HOLD` reader - the hold configure of rtc gpio0"]
pub type GPIO_PIN0_HOLD_R = crate::BitReader;
#[doc = "Field `GPIO_PIN0_HOLD` writer - the hold configure of rtc gpio0"]
pub type GPIO_PIN0_HOLD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_PIN1_HOLD` reader - the hold configure of rtc gpio1"]
pub type GPIO_PIN1_HOLD_R = crate::BitReader;
#[doc = "Field `GPIO_PIN1_HOLD` writer - the hold configure of rtc gpio1"]
pub type GPIO_PIN1_HOLD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_PIN2_HOLD` reader - the hold configure of rtc gpio2"]
pub type GPIO_PIN2_HOLD_R = crate::BitReader;
#[doc = "Field `GPIO_PIN2_HOLD` writer - the hold configure of rtc gpio2"]
pub type GPIO_PIN2_HOLD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_PIN3_HOLD` reader - the hold configure of rtc gpio3"]
pub type GPIO_PIN3_HOLD_R = crate::BitReader;
#[doc = "Field `GPIO_PIN3_HOLD` writer - the hold configure of rtc gpio3"]
pub type GPIO_PIN3_HOLD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_PIN4_HOLD` reader - the hold configure of rtc gpio4"]
pub type GPIO_PIN4_HOLD_R = crate::BitReader;
#[doc = "Field `GPIO_PIN4_HOLD` writer - the hold configure of rtc gpio4"]
pub type GPIO_PIN4_HOLD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GPIO_PIN5_HOLD` reader - the hold configure of rtc gpio5"]
pub type GPIO_PIN5_HOLD_R = crate::BitReader;
#[doc = "Field `GPIO_PIN5_HOLD` writer - the hold configure of rtc gpio5"]
pub type GPIO_PIN5_HOLD_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - the hold configure of rtc gpio0"]
    #[inline(always)]
    pub fn gpio_pin0_hold(&self) -> GPIO_PIN0_HOLD_R {
        GPIO_PIN0_HOLD_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - the hold configure of rtc gpio1"]
    #[inline(always)]
    pub fn gpio_pin1_hold(&self) -> GPIO_PIN1_HOLD_R {
        GPIO_PIN1_HOLD_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - the hold configure of rtc gpio2"]
    #[inline(always)]
    pub fn gpio_pin2_hold(&self) -> GPIO_PIN2_HOLD_R {
        GPIO_PIN2_HOLD_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - the hold configure of rtc gpio3"]
    #[inline(always)]
    pub fn gpio_pin3_hold(&self) -> GPIO_PIN3_HOLD_R {
        GPIO_PIN3_HOLD_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - the hold configure of rtc gpio4"]
    #[inline(always)]
    pub fn gpio_pin4_hold(&self) -> GPIO_PIN4_HOLD_R {
        GPIO_PIN4_HOLD_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - the hold configure of rtc gpio5"]
    #[inline(always)]
    pub fn gpio_pin5_hold(&self) -> GPIO_PIN5_HOLD_R {
        GPIO_PIN5_HOLD_R::new(((self.bits >> 5) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PAD_HOLD")
            .field("gpio_pin0_hold", &self.gpio_pin0_hold())
            .field("gpio_pin1_hold", &self.gpio_pin1_hold())
            .field("gpio_pin2_hold", &self.gpio_pin2_hold())
            .field("gpio_pin3_hold", &self.gpio_pin3_hold())
            .field("gpio_pin4_hold", &self.gpio_pin4_hold())
            .field("gpio_pin5_hold", &self.gpio_pin5_hold())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - the hold configure of rtc gpio0"]
    #[inline(always)]
    pub fn gpio_pin0_hold(&mut self) -> GPIO_PIN0_HOLD_W<'_, PAD_HOLD_SPEC> {
        GPIO_PIN0_HOLD_W::new(self, 0)
    }
    #[doc = "Bit 1 - the hold configure of rtc gpio1"]
    #[inline(always)]
    pub fn gpio_pin1_hold(&mut self) -> GPIO_PIN1_HOLD_W<'_, PAD_HOLD_SPEC> {
        GPIO_PIN1_HOLD_W::new(self, 1)
    }
    #[doc = "Bit 2 - the hold configure of rtc gpio2"]
    #[inline(always)]
    pub fn gpio_pin2_hold(&mut self) -> GPIO_PIN2_HOLD_W<'_, PAD_HOLD_SPEC> {
        GPIO_PIN2_HOLD_W::new(self, 2)
    }
    #[doc = "Bit 3 - the hold configure of rtc gpio3"]
    #[inline(always)]
    pub fn gpio_pin3_hold(&mut self) -> GPIO_PIN3_HOLD_W<'_, PAD_HOLD_SPEC> {
        GPIO_PIN3_HOLD_W::new(self, 3)
    }
    #[doc = "Bit 4 - the hold configure of rtc gpio4"]
    #[inline(always)]
    pub fn gpio_pin4_hold(&mut self) -> GPIO_PIN4_HOLD_W<'_, PAD_HOLD_SPEC> {
        GPIO_PIN4_HOLD_W::new(self, 4)
    }
    #[doc = "Bit 5 - the hold configure of rtc gpio5"]
    #[inline(always)]
    pub fn gpio_pin5_hold(&mut self) -> GPIO_PIN5_HOLD_W<'_, PAD_HOLD_SPEC> {
        GPIO_PIN5_HOLD_W::new(self, 5)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`pad_hold::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pad_hold::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PAD_HOLD_SPEC;
impl crate::RegisterSpec for PAD_HOLD_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pad_hold::R`](R) reader structure"]
impl crate::Readable for PAD_HOLD_SPEC {}
#[doc = "`write(|w| ..)` method takes [`pad_hold::W`](W) writer structure"]
impl crate::Writable for PAD_HOLD_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PAD_HOLD to value 0"]
impl crate::Resettable for PAD_HOLD_SPEC {}
