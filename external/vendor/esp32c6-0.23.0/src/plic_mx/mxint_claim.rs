#[doc = "Register `MXINT_CLAIM` reader"]
pub type R = crate::R<MXINT_CLAIM_SPEC>;
#[doc = "Register `MXINT_CLAIM` writer"]
pub type W = crate::W<MXINT_CLAIM_SPEC>;
#[doc = "Field `CPU_MXINT_CLAIM` reader - hp_mb_int is generated after writing 32'h20200721 to core0_lp_intr_flag."]
pub type CPU_MXINT_CLAIM_R = crate::FieldReader<u32>;
#[doc = "Field `CPU_MXINT_CLAIM` writer - hp_mb_int is generated after writing 32'h20200721 to core0_lp_intr_flag."]
pub type CPU_MXINT_CLAIM_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - hp_mb_int is generated after writing 32'h20200721 to core0_lp_intr_flag."]
    #[inline(always)]
    pub fn cpu_mxint_claim(&self) -> CPU_MXINT_CLAIM_R {
        CPU_MXINT_CLAIM_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MXINT_CLAIM")
            .field("cpu_mxint_claim", &self.cpu_mxint_claim())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - hp_mb_int is generated after writing 32'h20200721 to core0_lp_intr_flag."]
    #[inline(always)]
    pub fn cpu_mxint_claim(&mut self) -> CPU_MXINT_CLAIM_W<'_, MXINT_CLAIM_SPEC> {
        CPU_MXINT_CLAIM_W::new(self, 0)
    }
}
#[doc = "PLIC MX Interrupt Claim Register\n\nYou can [`read`](crate::Reg::read) this register and get [`mxint_claim::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mxint_claim::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MXINT_CLAIM_SPEC;
impl crate::RegisterSpec for MXINT_CLAIM_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mxint_claim::R`](R) reader structure"]
impl crate::Readable for MXINT_CLAIM_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mxint_claim::W`](W) writer structure"]
impl crate::Writable for MXINT_CLAIM_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MXINT_CLAIM to value 0"]
impl crate::Resettable for MXINT_CLAIM_SPEC {}
