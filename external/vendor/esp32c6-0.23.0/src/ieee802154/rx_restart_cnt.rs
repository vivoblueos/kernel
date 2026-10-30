#[doc = "Register `RX_RESTART_CNT` reader"]
pub type R = crate::R<RX_RESTART_CNT_SPEC>;
#[doc = "Register `RX_RESTART_CNT` writer"]
pub type W = crate::W<RX_RESTART_CNT_SPEC>;
#[doc = "Field `RX_RESTART_CNT` reader - "]
pub type RX_RESTART_CNT_R = crate::FieldReader<u16>;
#[doc = "Field `RX_RESTART_CNT` writer - "]
pub type RX_RESTART_CNT_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn rx_restart_cnt(&self) -> RX_RESTART_CNT_R {
        RX_RESTART_CNT_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RX_RESTART_CNT")
            .field("rx_restart_cnt", &self.rx_restart_cnt())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn rx_restart_cnt(&mut self) -> RX_RESTART_CNT_W<'_, RX_RESTART_CNT_SPEC> {
        RX_RESTART_CNT_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_restart_cnt::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_restart_cnt::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RX_RESTART_CNT_SPEC;
impl crate::RegisterSpec for RX_RESTART_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rx_restart_cnt::R`](R) reader structure"]
impl crate::Readable for RX_RESTART_CNT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rx_restart_cnt::W`](W) writer structure"]
impl crate::Writable for RX_RESTART_CNT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RX_RESTART_CNT to value 0"]
impl crate::Resettable for RX_RESTART_CNT_SPEC {}
