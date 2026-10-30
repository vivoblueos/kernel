#[doc = "Register `CORE_0_PIF_PMS_CONSTRAIN_9` reader"]
pub type R = crate::R<CORE_0_PIF_PMS_CONSTRAIN_9_SPEC>;
#[doc = "Register `CORE_0_PIF_PMS_CONSTRAIN_9` writer"]
pub type W = crate::W<CORE_0_PIF_PMS_CONSTRAIN_9_SPEC>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_0` reader - core_0_pif_pms_constrain_rtcfast_spltaddr_world_0"]
pub type CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_0_R = crate::FieldReader<u16>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_0` writer - core_0_pif_pms_constrain_rtcfast_spltaddr_world_0"]
pub type CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_0_W<'a, REG> =
    crate::FieldWriter<'a, REG, 11, u16>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_1` reader - core_0_pif_pms_constrain_rtcfast_spltaddr_world_1"]
pub type CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_1_R = crate::FieldReader<u16>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_1` writer - core_0_pif_pms_constrain_rtcfast_spltaddr_world_1"]
pub type CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_1_W<'a, REG> =
    crate::FieldWriter<'a, REG, 11, u16>;
impl R {
    #[doc = "Bits 0:10 - core_0_pif_pms_constrain_rtcfast_spltaddr_world_0"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_rtcfast_spltaddr_world_0(
        &self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_0_R {
        CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_0_R::new((self.bits & 0x07ff) as u16)
    }
    #[doc = "Bits 11:21 - core_0_pif_pms_constrain_rtcfast_spltaddr_world_1"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_rtcfast_spltaddr_world_1(
        &self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_1_R {
        CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_1_R::new(
            ((self.bits >> 11) & 0x07ff) as u16,
        )
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE_0_PIF_PMS_CONSTRAIN_9")
            .field(
                "core_0_pif_pms_constrain_rtcfast_spltaddr_world_0",
                &self.core_0_pif_pms_constrain_rtcfast_spltaddr_world_0(),
            )
            .field(
                "core_0_pif_pms_constrain_rtcfast_spltaddr_world_1",
                &self.core_0_pif_pms_constrain_rtcfast_spltaddr_world_1(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:10 - core_0_pif_pms_constrain_rtcfast_spltaddr_world_0"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_rtcfast_spltaddr_world_0(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_0_W<'_, CORE_0_PIF_PMS_CONSTRAIN_9_SPEC>
    {
        CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_0_W::new(self, 0)
    }
    #[doc = "Bits 11:21 - core_0_pif_pms_constrain_rtcfast_spltaddr_world_1"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_rtcfast_spltaddr_world_1(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_1_W<'_, CORE_0_PIF_PMS_CONSTRAIN_9_SPEC>
    {
        CORE_0_PIF_PMS_CONSTRAIN_RTCFAST_SPLTADDR_WORLD_1_W::new(self, 11)
    }
}
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_9_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_9::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_9::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE_0_PIF_PMS_CONSTRAIN_9_SPEC;
impl crate::RegisterSpec for CORE_0_PIF_PMS_CONSTRAIN_9_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core_0_pif_pms_constrain_9::R`](R) reader structure"]
impl crate::Readable for CORE_0_PIF_PMS_CONSTRAIN_9_SPEC {}
#[doc = "`write(|w| ..)` method takes [`core_0_pif_pms_constrain_9::W`](W) writer structure"]
impl crate::Writable for CORE_0_PIF_PMS_CONSTRAIN_9_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CORE_0_PIF_PMS_CONSTRAIN_9 to value 0x003f_ffff"]
impl crate::Resettable for CORE_0_PIF_PMS_CONSTRAIN_9_SPEC {
    const RESET_VALUE: u32 = 0x003f_ffff;
}
