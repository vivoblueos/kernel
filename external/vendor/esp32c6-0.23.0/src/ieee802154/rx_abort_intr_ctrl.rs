#[doc = "Register `RX_ABORT_INTR_CTRL` reader"]
pub type R = crate::R<RX_ABORT_INTR_CTRL_SPEC>;
#[doc = "Register `RX_ABORT_INTR_CTRL` writer"]
pub type W = crate::W<RX_ABORT_INTR_CTRL_SPEC>;
#[doc = "Field `RX_ABORT_INTR_CTRL` reader - "]
pub type RX_ABORT_INTR_CTRL_R = crate::FieldReader<u32>;
#[doc = "Field `RX_ABORT_INTR_CTRL` writer - "]
pub type RX_ABORT_INTR_CTRL_W<'a, REG> = crate::FieldWriter<'a, REG, 31, u32>;
impl R {
    #[doc = "Bits 0:30"]
    #[inline(always)]
    pub fn rx_abort_intr_ctrl(&self) -> RX_ABORT_INTR_CTRL_R {
        RX_ABORT_INTR_CTRL_R::new(self.bits & 0x7fff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RX_ABORT_INTR_CTRL")
            .field("rx_abort_intr_ctrl", &self.rx_abort_intr_ctrl())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:30"]
    #[inline(always)]
    pub fn rx_abort_intr_ctrl(&mut self) -> RX_ABORT_INTR_CTRL_W<'_, RX_ABORT_INTR_CTRL_SPEC> {
        RX_ABORT_INTR_CTRL_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_abort_intr_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_abort_intr_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RX_ABORT_INTR_CTRL_SPEC;
impl crate::RegisterSpec for RX_ABORT_INTR_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rx_abort_intr_ctrl::R`](R) reader structure"]
impl crate::Readable for RX_ABORT_INTR_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rx_abort_intr_ctrl::W`](W) writer structure"]
impl crate::Writable for RX_ABORT_INTR_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RX_ABORT_INTR_CTRL to value 0"]
impl crate::Resettable for RX_ABORT_INTR_CTRL_SPEC {}
