#[doc = "Register `ICACHE_PRELOCK_CTRL` reader"]
pub type R = crate::R<ICACHE_PRELOCK_CTRL_SPEC>;
#[doc = "Register `ICACHE_PRELOCK_CTRL` writer"]
pub type W = crate::W<ICACHE_PRELOCK_CTRL_SPEC>;
#[doc = "Field `ICACHE_PRELOCK_SCT0_EN` reader - The bit is used to enable the first section of prelock function."]
pub type ICACHE_PRELOCK_SCT0_EN_R = crate::BitReader;
#[doc = "Field `ICACHE_PRELOCK_SCT0_EN` writer - The bit is used to enable the first section of prelock function."]
pub type ICACHE_PRELOCK_SCT0_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ICACHE_PRELOCK_SCT1_EN` reader - The bit is used to enable the second section of prelock function."]
pub type ICACHE_PRELOCK_SCT1_EN_R = crate::BitReader;
#[doc = "Field `ICACHE_PRELOCK_SCT1_EN` writer - The bit is used to enable the second section of prelock function."]
pub type ICACHE_PRELOCK_SCT1_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The bit is used to enable the first section of prelock function."]
    #[inline(always)]
    pub fn icache_prelock_sct0_en(&self) -> ICACHE_PRELOCK_SCT0_EN_R {
        ICACHE_PRELOCK_SCT0_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to enable the second section of prelock function."]
    #[inline(always)]
    pub fn icache_prelock_sct1_en(&self) -> ICACHE_PRELOCK_SCT1_EN_R {
        ICACHE_PRELOCK_SCT1_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ICACHE_PRELOCK_CTRL")
            .field("icache_prelock_sct0_en", &self.icache_prelock_sct0_en())
            .field("icache_prelock_sct1_en", &self.icache_prelock_sct1_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to enable the first section of prelock function."]
    #[inline(always)]
    pub fn icache_prelock_sct0_en(
        &mut self,
    ) -> ICACHE_PRELOCK_SCT0_EN_W<'_, ICACHE_PRELOCK_CTRL_SPEC> {
        ICACHE_PRELOCK_SCT0_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - The bit is used to enable the second section of prelock function."]
    #[inline(always)]
    pub fn icache_prelock_sct1_en(
        &mut self,
    ) -> ICACHE_PRELOCK_SCT1_EN_W<'_, ICACHE_PRELOCK_CTRL_SPEC> {
        ICACHE_PRELOCK_SCT1_EN_W::new(self, 1)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_prelock_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_prelock_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ICACHE_PRELOCK_CTRL_SPEC;
impl crate::RegisterSpec for ICACHE_PRELOCK_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`icache_prelock_ctrl::R`](R) reader structure"]
impl crate::Readable for ICACHE_PRELOCK_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`icache_prelock_ctrl::W`](W) writer structure"]
impl crate::Writable for ICACHE_PRELOCK_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ICACHE_PRELOCK_CTRL to value 0"]
impl crate::Resettable for ICACHE_PRELOCK_CTRL_SPEC {}
