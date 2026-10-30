#[doc = "Register `GPIO_HOLD0` reader"]
pub type R = crate::R<GPIO_HOLD0_SPEC>;
#[doc = "Register `GPIO_HOLD0` writer"]
pub type W = crate::W<GPIO_HOLD0_SPEC>;
#[doc = "Field `GPIO_HOLD0` reader - need_des"]
pub type GPIO_HOLD0_R = crate::FieldReader<u32>;
#[doc = "Field `GPIO_HOLD0` writer - need_des"]
pub type GPIO_HOLD0_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn gpio_hold0(&self) -> GPIO_HOLD0_R {
        GPIO_HOLD0_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("GPIO_HOLD0")
            .field("gpio_hold0", &self.gpio_hold0())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn gpio_hold0(&mut self) -> GPIO_HOLD0_W<'_, GPIO_HOLD0_SPEC> {
        GPIO_HOLD0_W::new(self, 0)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`gpio_hold0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`gpio_hold0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GPIO_HOLD0_SPEC;
impl crate::RegisterSpec for GPIO_HOLD0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`gpio_hold0::R`](R) reader structure"]
impl crate::Readable for GPIO_HOLD0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`gpio_hold0::W`](W) writer structure"]
impl crate::Writable for GPIO_HOLD0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets GPIO_HOLD0 to value 0"]
impl crate::Resettable for GPIO_HOLD0_SPEC {}
