#[doc = "Register `TX_CCM_SCHEDULE_STATUS` reader"]
pub type R = crate::R<TX_CCM_SCHEDULE_STATUS_SPEC>;
#[doc = "Register `TX_CCM_SCHEDULE_STATUS` writer"]
pub type W = crate::W<TX_CCM_SCHEDULE_STATUS_SPEC>;
#[doc = "Field `TX_CCM_SCHEDULE_STATUS` reader - "]
pub type TX_CCM_SCHEDULE_STATUS_R = crate::FieldReader<u32>;
#[doc = "Field `TX_CCM_SCHEDULE_STATUS` writer - "]
pub type TX_CCM_SCHEDULE_STATUS_W<'a, REG> = crate::FieldWriter<'a, REG, 31, u32>;
impl R {
    #[doc = "Bits 0:30"]
    #[inline(always)]
    pub fn tx_ccm_schedule_status(&self) -> TX_CCM_SCHEDULE_STATUS_R {
        TX_CCM_SCHEDULE_STATUS_R::new(self.bits & 0x7fff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_CCM_SCHEDULE_STATUS")
            .field("tx_ccm_schedule_status", &self.tx_ccm_schedule_status())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:30"]
    #[inline(always)]
    pub fn tx_ccm_schedule_status(
        &mut self,
    ) -> TX_CCM_SCHEDULE_STATUS_W<'_, TX_CCM_SCHEDULE_STATUS_SPEC> {
        TX_CCM_SCHEDULE_STATUS_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_ccm_schedule_status::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_ccm_schedule_status::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_CCM_SCHEDULE_STATUS_SPEC;
impl crate::RegisterSpec for TX_CCM_SCHEDULE_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_ccm_schedule_status::R`](R) reader structure"]
impl crate::Readable for TX_CCM_SCHEDULE_STATUS_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_ccm_schedule_status::W`](W) writer structure"]
impl crate::Writable for TX_CCM_SCHEDULE_STATUS_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_CCM_SCHEDULE_STATUS to value 0"]
impl crate::Resettable for TX_CCM_SCHEDULE_STATUS_SPEC {}
