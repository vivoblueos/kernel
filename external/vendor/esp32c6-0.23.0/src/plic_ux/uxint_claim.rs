#[doc = "Register `UXINT_CLAIM` reader"]
pub type R = crate::R<UXINT_CLAIM_SPEC>;
#[doc = "Register `UXINT_CLAIM` writer"]
pub type W = crate::W<UXINT_CLAIM_SPEC>;
#[doc = "Field `CPU_UXINT_CLAIM` reader - hp_mb_int is generated after writing 32'h20200721 to core0_lp_intr_flag."]
pub type CPU_UXINT_CLAIM_R = crate::FieldReader<u32>;
#[doc = "Field `CPU_UXINT_CLAIM` writer - hp_mb_int is generated after writing 32'h20200721 to core0_lp_intr_flag."]
pub type CPU_UXINT_CLAIM_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - hp_mb_int is generated after writing 32'h20200721 to core0_lp_intr_flag."]
    #[inline(always)]
    pub fn cpu_uxint_claim(&self) -> CPU_UXINT_CLAIM_R {
        CPU_UXINT_CLAIM_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("UXINT_CLAIM")
            .field("cpu_uxint_claim", &self.cpu_uxint_claim())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - hp_mb_int is generated after writing 32'h20200721 to core0_lp_intr_flag."]
    #[inline(always)]
    pub fn cpu_uxint_claim(&mut self) -> CPU_UXINT_CLAIM_W<'_, UXINT_CLAIM_SPEC> {
        CPU_UXINT_CLAIM_W::new(self, 0)
    }
}
#[doc = "PLIC UX Interrupt Claim Register\n\nYou can [`read`](crate::Reg::read) this register and get [`uxint_claim::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uxint_claim::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct UXINT_CLAIM_SPEC;
impl crate::RegisterSpec for UXINT_CLAIM_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`uxint_claim::R`](R) reader structure"]
impl crate::Readable for UXINT_CLAIM_SPEC {}
#[doc = "`write(|w| ..)` method takes [`uxint_claim::W`](W) writer structure"]
impl crate::Writable for UXINT_CLAIM_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets UXINT_CLAIM to value 0"]
impl crate::Resettable for UXINT_CLAIM_SPEC {}
