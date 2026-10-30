#[doc = "Register `CONT_RX_DELAY` reader"]
pub type R = crate::R<CONT_RX_DELAY_SPEC>;
#[doc = "Register `CONT_RX_DELAY` writer"]
pub type W = crate::W<CONT_RX_DELAY_SPEC>;
#[doc = "Field `CONT_RX_DELAY` reader - "]
pub type CONT_RX_DELAY_R = crate::FieldReader;
#[doc = "Field `CONT_RX_DELAY` writer - "]
pub type CONT_RX_DELAY_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
impl R {
    #[doc = "Bits 0:5"]
    #[inline(always)]
    pub fn cont_rx_delay(&self) -> CONT_RX_DELAY_R {
        CONT_RX_DELAY_R::new((self.bits & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONT_RX_DELAY")
            .field("cont_rx_delay", &self.cont_rx_delay())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:5"]
    #[inline(always)]
    pub fn cont_rx_delay(&mut self) -> CONT_RX_DELAY_W<'_, CONT_RX_DELAY_SPEC> {
        CONT_RX_DELAY_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`cont_rx_delay::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cont_rx_delay::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONT_RX_DELAY_SPEC;
impl crate::RegisterSpec for CONT_RX_DELAY_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cont_rx_delay::R`](R) reader structure"]
impl crate::Readable for CONT_RX_DELAY_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cont_rx_delay::W`](W) writer structure"]
impl crate::Writable for CONT_RX_DELAY_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONT_RX_DELAY to value 0"]
impl crate::Resettable for CONT_RX_DELAY_SPEC {}
