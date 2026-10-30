#[doc = "Register `ICACHE_TAG_POWER_CTRL` reader"]
pub type R = crate::R<ICACHE_TAG_POWER_CTRL_SPEC>;
#[doc = "Register `ICACHE_TAG_POWER_CTRL` writer"]
pub type W = crate::W<ICACHE_TAG_POWER_CTRL_SPEC>;
#[doc = "Field `ICACHE_TAG_MEM_FORCE_ON` reader - The bit is used to close clock gating of icache tag memory. 1: close gating, 0: open clock gating."]
pub type ICACHE_TAG_MEM_FORCE_ON_R = crate::BitReader;
#[doc = "Field `ICACHE_TAG_MEM_FORCE_ON` writer - The bit is used to close clock gating of icache tag memory. 1: close gating, 0: open clock gating."]
pub type ICACHE_TAG_MEM_FORCE_ON_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ICACHE_TAG_MEM_FORCE_PD` reader - The bit is used to power icache tag memory down, 0: follow rtc_lslp, 1: power down"]
pub type ICACHE_TAG_MEM_FORCE_PD_R = crate::BitReader;
#[doc = "Field `ICACHE_TAG_MEM_FORCE_PD` writer - The bit is used to power icache tag memory down, 0: follow rtc_lslp, 1: power down"]
pub type ICACHE_TAG_MEM_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ICACHE_TAG_MEM_FORCE_PU` reader - The bit is used to power icache tag memory up, 0: follow rtc_lslp, 1: power up"]
pub type ICACHE_TAG_MEM_FORCE_PU_R = crate::BitReader;
#[doc = "Field `ICACHE_TAG_MEM_FORCE_PU` writer - The bit is used to power icache tag memory up, 0: follow rtc_lslp, 1: power up"]
pub type ICACHE_TAG_MEM_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The bit is used to close clock gating of icache tag memory. 1: close gating, 0: open clock gating."]
    #[inline(always)]
    pub fn icache_tag_mem_force_on(&self) -> ICACHE_TAG_MEM_FORCE_ON_R {
        ICACHE_TAG_MEM_FORCE_ON_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to power icache tag memory down, 0: follow rtc_lslp, 1: power down"]
    #[inline(always)]
    pub fn icache_tag_mem_force_pd(&self) -> ICACHE_TAG_MEM_FORCE_PD_R {
        ICACHE_TAG_MEM_FORCE_PD_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The bit is used to power icache tag memory up, 0: follow rtc_lslp, 1: power up"]
    #[inline(always)]
    pub fn icache_tag_mem_force_pu(&self) -> ICACHE_TAG_MEM_FORCE_PU_R {
        ICACHE_TAG_MEM_FORCE_PU_R::new(((self.bits >> 2) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ICACHE_TAG_POWER_CTRL")
            .field("icache_tag_mem_force_on", &self.icache_tag_mem_force_on())
            .field("icache_tag_mem_force_pd", &self.icache_tag_mem_force_pd())
            .field("icache_tag_mem_force_pu", &self.icache_tag_mem_force_pu())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to close clock gating of icache tag memory. 1: close gating, 0: open clock gating."]
    #[inline(always)]
    pub fn icache_tag_mem_force_on(
        &mut self,
    ) -> ICACHE_TAG_MEM_FORCE_ON_W<'_, ICACHE_TAG_POWER_CTRL_SPEC> {
        ICACHE_TAG_MEM_FORCE_ON_W::new(self, 0)
    }
    #[doc = "Bit 1 - The bit is used to power icache tag memory down, 0: follow rtc_lslp, 1: power down"]
    #[inline(always)]
    pub fn icache_tag_mem_force_pd(
        &mut self,
    ) -> ICACHE_TAG_MEM_FORCE_PD_W<'_, ICACHE_TAG_POWER_CTRL_SPEC> {
        ICACHE_TAG_MEM_FORCE_PD_W::new(self, 1)
    }
    #[doc = "Bit 2 - The bit is used to power icache tag memory up, 0: follow rtc_lslp, 1: power up"]
    #[inline(always)]
    pub fn icache_tag_mem_force_pu(
        &mut self,
    ) -> ICACHE_TAG_MEM_FORCE_PU_W<'_, ICACHE_TAG_POWER_CTRL_SPEC> {
        ICACHE_TAG_MEM_FORCE_PU_W::new(self, 2)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_tag_power_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_tag_power_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ICACHE_TAG_POWER_CTRL_SPEC;
impl crate::RegisterSpec for ICACHE_TAG_POWER_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`icache_tag_power_ctrl::R`](R) reader structure"]
impl crate::Readable for ICACHE_TAG_POWER_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`icache_tag_power_ctrl::W`](W) writer structure"]
impl crate::Writable for ICACHE_TAG_POWER_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ICACHE_TAG_POWER_CTRL to value 0x05"]
impl crate::Resettable for ICACHE_TAG_POWER_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x05;
}
