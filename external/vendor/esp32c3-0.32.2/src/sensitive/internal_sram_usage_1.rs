#[doc = "Register `INTERNAL_SRAM_USAGE_1` reader"]
pub type R = crate::R<INTERNAL_SRAM_USAGE_1_SPEC>;
#[doc = "Register `INTERNAL_SRAM_USAGE_1` writer"]
pub type W = crate::W<INTERNAL_SRAM_USAGE_1_SPEC>;
#[doc = "Field `INTERNAL_SRAM_USAGE_CPU_CACHE` reader - internal_sram_usage_cpu_cache"]
pub type INTERNAL_SRAM_USAGE_CPU_CACHE_R = crate::BitReader;
#[doc = "Field `INTERNAL_SRAM_USAGE_CPU_CACHE` writer - internal_sram_usage_cpu_cache"]
pub type INTERNAL_SRAM_USAGE_CPU_CACHE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `INTERNAL_SRAM_USAGE_CPU_SRAM` reader - internal_sram_usage_cpu_sram"]
pub type INTERNAL_SRAM_USAGE_CPU_SRAM_R = crate::FieldReader;
#[doc = "Field `INTERNAL_SRAM_USAGE_CPU_SRAM` writer - internal_sram_usage_cpu_sram"]
pub type INTERNAL_SRAM_USAGE_CPU_SRAM_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
impl R {
    #[doc = "Bit 0 - internal_sram_usage_cpu_cache"]
    #[inline(always)]
    pub fn internal_sram_usage_cpu_cache(&self) -> INTERNAL_SRAM_USAGE_CPU_CACHE_R {
        INTERNAL_SRAM_USAGE_CPU_CACHE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:3 - internal_sram_usage_cpu_sram"]
    #[inline(always)]
    pub fn internal_sram_usage_cpu_sram(&self) -> INTERNAL_SRAM_USAGE_CPU_SRAM_R {
        INTERNAL_SRAM_USAGE_CPU_SRAM_R::new(((self.bits >> 1) & 7) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INTERNAL_SRAM_USAGE_1")
            .field(
                "internal_sram_usage_cpu_cache",
                &self.internal_sram_usage_cpu_cache(),
            )
            .field(
                "internal_sram_usage_cpu_sram",
                &self.internal_sram_usage_cpu_sram(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - internal_sram_usage_cpu_cache"]
    #[inline(always)]
    pub fn internal_sram_usage_cpu_cache(
        &mut self,
    ) -> INTERNAL_SRAM_USAGE_CPU_CACHE_W<'_, INTERNAL_SRAM_USAGE_1_SPEC> {
        INTERNAL_SRAM_USAGE_CPU_CACHE_W::new(self, 0)
    }
    #[doc = "Bits 1:3 - internal_sram_usage_cpu_sram"]
    #[inline(always)]
    pub fn internal_sram_usage_cpu_sram(
        &mut self,
    ) -> INTERNAL_SRAM_USAGE_CPU_SRAM_W<'_, INTERNAL_SRAM_USAGE_1_SPEC> {
        INTERNAL_SRAM_USAGE_CPU_SRAM_W::new(self, 1)
    }
}
#[doc = "SENSITIVE_INTERNAL_SRAM_USAGE_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`internal_sram_usage_1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`internal_sram_usage_1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INTERNAL_SRAM_USAGE_1_SPEC;
impl crate::RegisterSpec for INTERNAL_SRAM_USAGE_1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`internal_sram_usage_1::R`](R) reader structure"]
impl crate::Readable for INTERNAL_SRAM_USAGE_1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`internal_sram_usage_1::W`](W) writer structure"]
impl crate::Writable for INTERNAL_SRAM_USAGE_1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INTERNAL_SRAM_USAGE_1 to value 0x0f"]
impl crate::Resettable for INTERNAL_SRAM_USAGE_1_SPEC {
    const RESET_VALUE: u32 = 0x0f;
}
