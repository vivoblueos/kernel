#[doc = "Register `CORE_0_PIF_PMS_MONITOR_4` reader"]
pub type R = crate::R<CORE_0_PIF_PMS_MONITOR_4_SPEC>;
#[doc = "Register `CORE_0_PIF_PMS_MONITOR_4` writer"]
pub type W = crate::W<CORE_0_PIF_PMS_MONITOR_4_SPEC>;
#[doc = "Field `CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_CLR` reader - core_0_pif_pms_monitor_nonword_violate_clr"]
pub type CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_CLR_R = crate::BitReader;
#[doc = "Field `CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_CLR` writer - core_0_pif_pms_monitor_nonword_violate_clr"]
pub type CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_EN` reader - core_0_pif_pms_monitor_nonword_violate_en"]
pub type CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_EN_R = crate::BitReader;
#[doc = "Field `CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_EN` writer - core_0_pif_pms_monitor_nonword_violate_en"]
pub type CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - core_0_pif_pms_monitor_nonword_violate_clr"]
    #[inline(always)]
    pub fn core_0_pif_pms_monitor_nonword_violate_clr(
        &self,
    ) -> CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_CLR_R {
        CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_CLR_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - core_0_pif_pms_monitor_nonword_violate_en"]
    #[inline(always)]
    pub fn core_0_pif_pms_monitor_nonword_violate_en(
        &self,
    ) -> CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_EN_R {
        CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE_0_PIF_PMS_MONITOR_4")
            .field(
                "core_0_pif_pms_monitor_nonword_violate_clr",
                &self.core_0_pif_pms_monitor_nonword_violate_clr(),
            )
            .field(
                "core_0_pif_pms_monitor_nonword_violate_en",
                &self.core_0_pif_pms_monitor_nonword_violate_en(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - core_0_pif_pms_monitor_nonword_violate_clr"]
    #[inline(always)]
    pub fn core_0_pif_pms_monitor_nonword_violate_clr(
        &mut self,
    ) -> CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_CLR_W<'_, CORE_0_PIF_PMS_MONITOR_4_SPEC> {
        CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_CLR_W::new(self, 0)
    }
    #[doc = "Bit 1 - core_0_pif_pms_monitor_nonword_violate_en"]
    #[inline(always)]
    pub fn core_0_pif_pms_monitor_nonword_violate_en(
        &mut self,
    ) -> CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_EN_W<'_, CORE_0_PIF_PMS_MONITOR_4_SPEC> {
        CORE_0_PIF_PMS_MONITOR_NONWORD_VIOLATE_EN_W::new(self, 1)
    }
}
#[doc = "SENSITIVE_CORE_0_PIF_PMS_MONITOR_4_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_monitor_4::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_monitor_4::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE_0_PIF_PMS_MONITOR_4_SPEC;
impl crate::RegisterSpec for CORE_0_PIF_PMS_MONITOR_4_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core_0_pif_pms_monitor_4::R`](R) reader structure"]
impl crate::Readable for CORE_0_PIF_PMS_MONITOR_4_SPEC {}
#[doc = "`write(|w| ..)` method takes [`core_0_pif_pms_monitor_4::W`](W) writer structure"]
impl crate::Writable for CORE_0_PIF_PMS_MONITOR_4_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CORE_0_PIF_PMS_MONITOR_4 to value 0x03"]
impl crate::Resettable for CORE_0_PIF_PMS_MONITOR_4_SPEC {
    const RESET_VALUE: u32 = 0x03;
}
