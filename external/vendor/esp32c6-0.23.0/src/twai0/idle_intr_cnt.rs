#[doc = "Register `IDLE_INTR_CNT` reader"]
pub type R = crate::R<IDLE_INTR_CNT_SPEC>;
#[doc = "Register `IDLE_INTR_CNT` writer"]
pub type W = crate::W<IDLE_INTR_CNT_SPEC>;
#[doc = "Field `IDLE_INTR_CNT` reader - Configure the number of cycles before triggering idle interrupt."]
pub type IDLE_INTR_CNT_R = crate::FieldReader<u32>;
#[doc = "Field `IDLE_INTR_CNT` writer - Configure the number of cycles before triggering idle interrupt."]
pub type IDLE_INTR_CNT_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Configure the number of cycles before triggering idle interrupt."]
    #[inline(always)]
    pub fn idle_intr_cnt(&self) -> IDLE_INTR_CNT_R {
        IDLE_INTR_CNT_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IDLE_INTR_CNT")
            .field("idle_intr_cnt", &self.idle_intr_cnt())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Configure the number of cycles before triggering idle interrupt."]
    #[inline(always)]
    pub fn idle_intr_cnt(&mut self) -> IDLE_INTR_CNT_W<'_, IDLE_INTR_CNT_SPEC> {
        IDLE_INTR_CNT_W::new(self, 0)
    }
}
#[doc = "Configure idle interrupt counter.\n\nYou can [`read`](crate::Reg::read) this register and get [`idle_intr_cnt::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`idle_intr_cnt::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IDLE_INTR_CNT_SPEC;
impl crate::RegisterSpec for IDLE_INTR_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`idle_intr_cnt::R`](R) reader structure"]
impl crate::Readable for IDLE_INTR_CNT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`idle_intr_cnt::W`](W) writer structure"]
impl crate::Writable for IDLE_INTR_CNT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IDLE_INTR_CNT to value 0x01"]
impl crate::Resettable for IDLE_INTR_CNT_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
