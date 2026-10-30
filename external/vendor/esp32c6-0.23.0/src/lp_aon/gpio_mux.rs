#[doc = "Register `GPIO_MUX` reader"]
pub type R = crate::R<GPIO_MUX_SPEC>;
#[doc = "Register `GPIO_MUX` writer"]
pub type W = crate::W<GPIO_MUX_SPEC>;
#[doc = "Field `SEL` reader - need_des"]
pub type SEL_R = crate::FieldReader;
#[doc = "Field `SEL` writer - need_des"]
pub type SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - need_des"]
    #[inline(always)]
    pub fn sel(&self) -> SEL_R {
        SEL_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("GPIO_MUX")
            .field("sel", &self.sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - need_des"]
    #[inline(always)]
    pub fn sel(&mut self) -> SEL_W<'_, GPIO_MUX_SPEC> {
        SEL_W::new(self, 0)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`gpio_mux::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`gpio_mux::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GPIO_MUX_SPEC;
impl crate::RegisterSpec for GPIO_MUX_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`gpio_mux::R`](R) reader structure"]
impl crate::Readable for GPIO_MUX_SPEC {}
#[doc = "`write(|w| ..)` method takes [`gpio_mux::W`](W) writer structure"]
impl crate::Writable for GPIO_MUX_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets GPIO_MUX to value 0"]
impl crate::Resettable for GPIO_MUX_SPEC {}
