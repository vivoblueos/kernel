#[doc = "Register `INTERNAL_SRAM_USAGE_4` reader"]
pub type R = crate::R<INTERNAL_SRAM_USAGE_4_SPEC>;
#[doc = "Register `INTERNAL_SRAM_USAGE_4` writer"]
pub type W = crate::W<INTERNAL_SRAM_USAGE_4_SPEC>;
#[doc = "Field `INTERNAL_SRAM_USAGE_LOG_SRAM` reader - internal_sram_usage_log_sram"]
pub type INTERNAL_SRAM_USAGE_LOG_SRAM_R = crate::BitReader;
#[doc = "Field `INTERNAL_SRAM_USAGE_LOG_SRAM` writer - internal_sram_usage_log_sram"]
pub type INTERNAL_SRAM_USAGE_LOG_SRAM_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - internal_sram_usage_log_sram"]
    #[inline(always)]
    pub fn internal_sram_usage_log_sram(&self) -> INTERNAL_SRAM_USAGE_LOG_SRAM_R {
        INTERNAL_SRAM_USAGE_LOG_SRAM_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INTERNAL_SRAM_USAGE_4")
            .field(
                "internal_sram_usage_log_sram",
                &self.internal_sram_usage_log_sram(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - internal_sram_usage_log_sram"]
    #[inline(always)]
    pub fn internal_sram_usage_log_sram(
        &mut self,
    ) -> INTERNAL_SRAM_USAGE_LOG_SRAM_W<'_, INTERNAL_SRAM_USAGE_4_SPEC> {
        INTERNAL_SRAM_USAGE_LOG_SRAM_W::new(self, 0)
    }
}
#[doc = "SENSITIVE_INTERNAL_SRAM_USAGE_4_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`internal_sram_usage_4::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`internal_sram_usage_4::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INTERNAL_SRAM_USAGE_4_SPEC;
impl crate::RegisterSpec for INTERNAL_SRAM_USAGE_4_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`internal_sram_usage_4::R`](R) reader structure"]
impl crate::Readable for INTERNAL_SRAM_USAGE_4_SPEC {}
#[doc = "`write(|w| ..)` method takes [`internal_sram_usage_4::W`](W) writer structure"]
impl crate::Writable for INTERNAL_SRAM_USAGE_4_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INTERNAL_SRAM_USAGE_4 to value 0"]
impl crate::Resettable for INTERNAL_SRAM_USAGE_4_SPEC {}
