#[doc = "Register `POWER_PD_HPWIFI_CNTL` reader"]
pub type R = crate::R<POWER_PD_HPWIFI_CNTL_SPEC>;
#[doc = "Register `POWER_PD_HPWIFI_CNTL` writer"]
pub type W = crate::W<POWER_PD_HPWIFI_CNTL_SPEC>;
#[doc = "Field `FORCE_HP_WIFI_RESET` reader - need_des"]
pub type FORCE_HP_WIFI_RESET_R = crate::BitReader;
#[doc = "Field `FORCE_HP_WIFI_RESET` writer - need_des"]
pub type FORCE_HP_WIFI_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FORCE_HP_WIFI_ISO` reader - need_des"]
pub type FORCE_HP_WIFI_ISO_R = crate::BitReader;
#[doc = "Field `FORCE_HP_WIFI_ISO` writer - need_des"]
pub type FORCE_HP_WIFI_ISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FORCE_HP_WIFI_PU` reader - need_des"]
pub type FORCE_HP_WIFI_PU_R = crate::BitReader;
#[doc = "Field `FORCE_HP_WIFI_PU` writer - need_des"]
pub type FORCE_HP_WIFI_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FORCE_HP_WIFI_NO_RESET` reader - need_des"]
pub type FORCE_HP_WIFI_NO_RESET_R = crate::BitReader;
#[doc = "Field `FORCE_HP_WIFI_NO_RESET` writer - need_des"]
pub type FORCE_HP_WIFI_NO_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FORCE_HP_WIFI_NO_ISO` reader - need_des"]
pub type FORCE_HP_WIFI_NO_ISO_R = crate::BitReader;
#[doc = "Field `FORCE_HP_WIFI_NO_ISO` writer - need_des"]
pub type FORCE_HP_WIFI_NO_ISO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FORCE_HP_WIFI_PD` reader - need_des"]
pub type FORCE_HP_WIFI_PD_R = crate::BitReader;
#[doc = "Field `FORCE_HP_WIFI_PD` writer - need_des"]
pub type FORCE_HP_WIFI_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PD_HP_WIFI_MASK` reader - need_des"]
pub type PD_HP_WIFI_MASK_R = crate::FieldReader;
#[doc = "Field `PD_HP_WIFI_MASK` writer - need_des"]
pub type PD_HP_WIFI_MASK_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `PD_HP_WIFI_PD_MASK` reader - need_des"]
pub type PD_HP_WIFI_PD_MASK_R = crate::FieldReader;
#[doc = "Field `PD_HP_WIFI_PD_MASK` writer - need_des"]
pub type PD_HP_WIFI_PD_MASK_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
impl R {
    #[doc = "Bit 0 - need_des"]
    #[inline(always)]
    pub fn force_hp_wifi_reset(&self) -> FORCE_HP_WIFI_RESET_R {
        FORCE_HP_WIFI_RESET_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - need_des"]
    #[inline(always)]
    pub fn force_hp_wifi_iso(&self) -> FORCE_HP_WIFI_ISO_R {
        FORCE_HP_WIFI_ISO_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - need_des"]
    #[inline(always)]
    pub fn force_hp_wifi_pu(&self) -> FORCE_HP_WIFI_PU_R {
        FORCE_HP_WIFI_PU_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - need_des"]
    #[inline(always)]
    pub fn force_hp_wifi_no_reset(&self) -> FORCE_HP_WIFI_NO_RESET_R {
        FORCE_HP_WIFI_NO_RESET_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - need_des"]
    #[inline(always)]
    pub fn force_hp_wifi_no_iso(&self) -> FORCE_HP_WIFI_NO_ISO_R {
        FORCE_HP_WIFI_NO_ISO_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - need_des"]
    #[inline(always)]
    pub fn force_hp_wifi_pd(&self) -> FORCE_HP_WIFI_PD_R {
        FORCE_HP_WIFI_PD_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bits 6:10 - need_des"]
    #[inline(always)]
    pub fn pd_hp_wifi_mask(&self) -> PD_HP_WIFI_MASK_R {
        PD_HP_WIFI_MASK_R::new(((self.bits >> 6) & 0x1f) as u8)
    }
    #[doc = "Bits 27:31 - need_des"]
    #[inline(always)]
    pub fn pd_hp_wifi_pd_mask(&self) -> PD_HP_WIFI_PD_MASK_R {
        PD_HP_WIFI_PD_MASK_R::new(((self.bits >> 27) & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("POWER_PD_HPWIFI_CNTL")
            .field("force_hp_wifi_reset", &self.force_hp_wifi_reset())
            .field("force_hp_wifi_iso", &self.force_hp_wifi_iso())
            .field("force_hp_wifi_pu", &self.force_hp_wifi_pu())
            .field("force_hp_wifi_no_reset", &self.force_hp_wifi_no_reset())
            .field("force_hp_wifi_no_iso", &self.force_hp_wifi_no_iso())
            .field("force_hp_wifi_pd", &self.force_hp_wifi_pd())
            .field("pd_hp_wifi_mask", &self.pd_hp_wifi_mask())
            .field("pd_hp_wifi_pd_mask", &self.pd_hp_wifi_pd_mask())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - need_des"]
    #[inline(always)]
    pub fn force_hp_wifi_reset(&mut self) -> FORCE_HP_WIFI_RESET_W<'_, POWER_PD_HPWIFI_CNTL_SPEC> {
        FORCE_HP_WIFI_RESET_W::new(self, 0)
    }
    #[doc = "Bit 1 - need_des"]
    #[inline(always)]
    pub fn force_hp_wifi_iso(&mut self) -> FORCE_HP_WIFI_ISO_W<'_, POWER_PD_HPWIFI_CNTL_SPEC> {
        FORCE_HP_WIFI_ISO_W::new(self, 1)
    }
    #[doc = "Bit 2 - need_des"]
    #[inline(always)]
    pub fn force_hp_wifi_pu(&mut self) -> FORCE_HP_WIFI_PU_W<'_, POWER_PD_HPWIFI_CNTL_SPEC> {
        FORCE_HP_WIFI_PU_W::new(self, 2)
    }
    #[doc = "Bit 3 - need_des"]
    #[inline(always)]
    pub fn force_hp_wifi_no_reset(
        &mut self,
    ) -> FORCE_HP_WIFI_NO_RESET_W<'_, POWER_PD_HPWIFI_CNTL_SPEC> {
        FORCE_HP_WIFI_NO_RESET_W::new(self, 3)
    }
    #[doc = "Bit 4 - need_des"]
    #[inline(always)]
    pub fn force_hp_wifi_no_iso(
        &mut self,
    ) -> FORCE_HP_WIFI_NO_ISO_W<'_, POWER_PD_HPWIFI_CNTL_SPEC> {
        FORCE_HP_WIFI_NO_ISO_W::new(self, 4)
    }
    #[doc = "Bit 5 - need_des"]
    #[inline(always)]
    pub fn force_hp_wifi_pd(&mut self) -> FORCE_HP_WIFI_PD_W<'_, POWER_PD_HPWIFI_CNTL_SPEC> {
        FORCE_HP_WIFI_PD_W::new(self, 5)
    }
    #[doc = "Bits 6:10 - need_des"]
    #[inline(always)]
    pub fn pd_hp_wifi_mask(&mut self) -> PD_HP_WIFI_MASK_W<'_, POWER_PD_HPWIFI_CNTL_SPEC> {
        PD_HP_WIFI_MASK_W::new(self, 6)
    }
    #[doc = "Bits 27:31 - need_des"]
    #[inline(always)]
    pub fn pd_hp_wifi_pd_mask(&mut self) -> PD_HP_WIFI_PD_MASK_W<'_, POWER_PD_HPWIFI_CNTL_SPEC> {
        PD_HP_WIFI_PD_MASK_W::new(self, 27)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`power_pd_hpwifi_cntl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`power_pd_hpwifi_cntl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct POWER_PD_HPWIFI_CNTL_SPEC;
impl crate::RegisterSpec for POWER_PD_HPWIFI_CNTL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`power_pd_hpwifi_cntl::R`](R) reader structure"]
impl crate::Readable for POWER_PD_HPWIFI_CNTL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`power_pd_hpwifi_cntl::W`](W) writer structure"]
impl crate::Writable for POWER_PD_HPWIFI_CNTL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets POWER_PD_HPWIFI_CNTL to value 0x1c"]
impl crate::Resettable for POWER_PD_HPWIFI_CNTL_SPEC {
    const RESET_VALUE: u32 = 0x1c;
}
