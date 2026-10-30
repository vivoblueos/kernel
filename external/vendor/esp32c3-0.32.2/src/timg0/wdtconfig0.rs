#[doc = "Register `WDTCONFIG0` reader"]
pub type R = crate::R<WDTCONFIG0_SPEC>;
#[doc = "Register `WDTCONFIG0` writer"]
pub type W = crate::W<WDTCONFIG0_SPEC>;
#[doc = "Field `WDT_APPCPU_RESET_EN` reader - reg_wdt_appcpu_reset_en."]
pub type WDT_APPCPU_RESET_EN_R = crate::BitReader;
#[doc = "Field `WDT_APPCPU_RESET_EN` writer - reg_wdt_appcpu_reset_en."]
pub type WDT_APPCPU_RESET_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WDT_PROCPU_RESET_EN` reader - reg_wdt_procpu_reset_en."]
pub type WDT_PROCPU_RESET_EN_R = crate::BitReader;
#[doc = "Field `WDT_PROCPU_RESET_EN` writer - reg_wdt_procpu_reset_en."]
pub type WDT_PROCPU_RESET_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WDT_FLASHBOOT_MOD_EN` reader - reg_wdt_flashboot_mod_en."]
pub type WDT_FLASHBOOT_MOD_EN_R = crate::BitReader;
#[doc = "Field `WDT_FLASHBOOT_MOD_EN` writer - reg_wdt_flashboot_mod_en."]
pub type WDT_FLASHBOOT_MOD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WDT_SYS_RESET_LENGTH` reader - reg_wdt_sys_reset_length."]
pub type WDT_SYS_RESET_LENGTH_R = crate::FieldReader;
#[doc = "Field `WDT_SYS_RESET_LENGTH` writer - reg_wdt_sys_reset_length."]
pub type WDT_SYS_RESET_LENGTH_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `WDT_CPU_RESET_LENGTH` reader - reg_wdt_cpu_reset_length."]
pub type WDT_CPU_RESET_LENGTH_R = crate::FieldReader;
#[doc = "Field `WDT_CPU_RESET_LENGTH` writer - reg_wdt_cpu_reset_length."]
pub type WDT_CPU_RESET_LENGTH_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `WDT_USE_XTAL` reader - reg_wdt_use_xtal."]
pub type WDT_USE_XTAL_R = crate::BitReader;
#[doc = "Field `WDT_USE_XTAL` writer - reg_wdt_use_xtal."]
pub type WDT_USE_XTAL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WDT_CONF_UPDATE_EN` writer - reg_wdt_conf_update_en."]
pub type WDT_CONF_UPDATE_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WDT_STG3` reader - reg_wdt_stg3."]
pub type WDT_STG3_R = crate::FieldReader;
#[doc = "Field `WDT_STG3` writer - reg_wdt_stg3."]
pub type WDT_STG3_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `WDT_STG2` reader - reg_wdt_stg2."]
pub type WDT_STG2_R = crate::FieldReader;
#[doc = "Field `WDT_STG2` writer - reg_wdt_stg2."]
pub type WDT_STG2_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `WDT_STG1` reader - reg_wdt_stg1."]
pub type WDT_STG1_R = crate::FieldReader;
#[doc = "Field `WDT_STG1` writer - reg_wdt_stg1."]
pub type WDT_STG1_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `WDT_STG0` reader - reg_wdt_stg0."]
pub type WDT_STG0_R = crate::FieldReader;
#[doc = "Field `WDT_STG0` writer - reg_wdt_stg0."]
pub type WDT_STG0_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `WDT_EN` reader - reg_wdt_en."]
pub type WDT_EN_R = crate::BitReader;
#[doc = "Field `WDT_EN` writer - reg_wdt_en."]
pub type WDT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 12 - reg_wdt_appcpu_reset_en."]
    #[inline(always)]
    pub fn wdt_appcpu_reset_en(&self) -> WDT_APPCPU_RESET_EN_R {
        WDT_APPCPU_RESET_EN_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - reg_wdt_procpu_reset_en."]
    #[inline(always)]
    pub fn wdt_procpu_reset_en(&self) -> WDT_PROCPU_RESET_EN_R {
        WDT_PROCPU_RESET_EN_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - reg_wdt_flashboot_mod_en."]
    #[inline(always)]
    pub fn wdt_flashboot_mod_en(&self) -> WDT_FLASHBOOT_MOD_EN_R {
        WDT_FLASHBOOT_MOD_EN_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bits 15:17 - reg_wdt_sys_reset_length."]
    #[inline(always)]
    pub fn wdt_sys_reset_length(&self) -> WDT_SYS_RESET_LENGTH_R {
        WDT_SYS_RESET_LENGTH_R::new(((self.bits >> 15) & 7) as u8)
    }
    #[doc = "Bits 18:20 - reg_wdt_cpu_reset_length."]
    #[inline(always)]
    pub fn wdt_cpu_reset_length(&self) -> WDT_CPU_RESET_LENGTH_R {
        WDT_CPU_RESET_LENGTH_R::new(((self.bits >> 18) & 7) as u8)
    }
    #[doc = "Bit 21 - reg_wdt_use_xtal."]
    #[inline(always)]
    pub fn wdt_use_xtal(&self) -> WDT_USE_XTAL_R {
        WDT_USE_XTAL_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bits 23:24 - reg_wdt_stg3."]
    #[inline(always)]
    pub fn wdt_stg3(&self) -> WDT_STG3_R {
        WDT_STG3_R::new(((self.bits >> 23) & 3) as u8)
    }
    #[doc = "Bits 25:26 - reg_wdt_stg2."]
    #[inline(always)]
    pub fn wdt_stg2(&self) -> WDT_STG2_R {
        WDT_STG2_R::new(((self.bits >> 25) & 3) as u8)
    }
    #[doc = "Bits 27:28 - reg_wdt_stg1."]
    #[inline(always)]
    pub fn wdt_stg1(&self) -> WDT_STG1_R {
        WDT_STG1_R::new(((self.bits >> 27) & 3) as u8)
    }
    #[doc = "Bits 29:30 - reg_wdt_stg0."]
    #[inline(always)]
    pub fn wdt_stg0(&self) -> WDT_STG0_R {
        WDT_STG0_R::new(((self.bits >> 29) & 3) as u8)
    }
    #[doc = "Bit 31 - reg_wdt_en."]
    #[inline(always)]
    pub fn wdt_en(&self) -> WDT_EN_R {
        WDT_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("WDTCONFIG0")
            .field("wdt_appcpu_reset_en", &self.wdt_appcpu_reset_en())
            .field("wdt_procpu_reset_en", &self.wdt_procpu_reset_en())
            .field("wdt_flashboot_mod_en", &self.wdt_flashboot_mod_en())
            .field("wdt_sys_reset_length", &self.wdt_sys_reset_length())
            .field("wdt_cpu_reset_length", &self.wdt_cpu_reset_length())
            .field("wdt_use_xtal", &self.wdt_use_xtal())
            .field("wdt_stg3", &self.wdt_stg3())
            .field("wdt_stg2", &self.wdt_stg2())
            .field("wdt_stg1", &self.wdt_stg1())
            .field("wdt_stg0", &self.wdt_stg0())
            .field("wdt_en", &self.wdt_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 12 - reg_wdt_appcpu_reset_en."]
    #[inline(always)]
    pub fn wdt_appcpu_reset_en(&mut self) -> WDT_APPCPU_RESET_EN_W<'_, WDTCONFIG0_SPEC> {
        WDT_APPCPU_RESET_EN_W::new(self, 12)
    }
    #[doc = "Bit 13 - reg_wdt_procpu_reset_en."]
    #[inline(always)]
    pub fn wdt_procpu_reset_en(&mut self) -> WDT_PROCPU_RESET_EN_W<'_, WDTCONFIG0_SPEC> {
        WDT_PROCPU_RESET_EN_W::new(self, 13)
    }
    #[doc = "Bit 14 - reg_wdt_flashboot_mod_en."]
    #[inline(always)]
    pub fn wdt_flashboot_mod_en(&mut self) -> WDT_FLASHBOOT_MOD_EN_W<'_, WDTCONFIG0_SPEC> {
        WDT_FLASHBOOT_MOD_EN_W::new(self, 14)
    }
    #[doc = "Bits 15:17 - reg_wdt_sys_reset_length."]
    #[inline(always)]
    pub fn wdt_sys_reset_length(&mut self) -> WDT_SYS_RESET_LENGTH_W<'_, WDTCONFIG0_SPEC> {
        WDT_SYS_RESET_LENGTH_W::new(self, 15)
    }
    #[doc = "Bits 18:20 - reg_wdt_cpu_reset_length."]
    #[inline(always)]
    pub fn wdt_cpu_reset_length(&mut self) -> WDT_CPU_RESET_LENGTH_W<'_, WDTCONFIG0_SPEC> {
        WDT_CPU_RESET_LENGTH_W::new(self, 18)
    }
    #[doc = "Bit 21 - reg_wdt_use_xtal."]
    #[inline(always)]
    pub fn wdt_use_xtal(&mut self) -> WDT_USE_XTAL_W<'_, WDTCONFIG0_SPEC> {
        WDT_USE_XTAL_W::new(self, 21)
    }
    #[doc = "Bit 22 - reg_wdt_conf_update_en."]
    #[inline(always)]
    pub fn wdt_conf_update_en(&mut self) -> WDT_CONF_UPDATE_EN_W<'_, WDTCONFIG0_SPEC> {
        WDT_CONF_UPDATE_EN_W::new(self, 22)
    }
    #[doc = "Bits 23:24 - reg_wdt_stg3."]
    #[inline(always)]
    pub fn wdt_stg3(&mut self) -> WDT_STG3_W<'_, WDTCONFIG0_SPEC> {
        WDT_STG3_W::new(self, 23)
    }
    #[doc = "Bits 25:26 - reg_wdt_stg2."]
    #[inline(always)]
    pub fn wdt_stg2(&mut self) -> WDT_STG2_W<'_, WDTCONFIG0_SPEC> {
        WDT_STG2_W::new(self, 25)
    }
    #[doc = "Bits 27:28 - reg_wdt_stg1."]
    #[inline(always)]
    pub fn wdt_stg1(&mut self) -> WDT_STG1_W<'_, WDTCONFIG0_SPEC> {
        WDT_STG1_W::new(self, 27)
    }
    #[doc = "Bits 29:30 - reg_wdt_stg0."]
    #[inline(always)]
    pub fn wdt_stg0(&mut self) -> WDT_STG0_W<'_, WDTCONFIG0_SPEC> {
        WDT_STG0_W::new(self, 29)
    }
    #[doc = "Bit 31 - reg_wdt_en."]
    #[inline(always)]
    pub fn wdt_en(&mut self) -> WDT_EN_W<'_, WDTCONFIG0_SPEC> {
        WDT_EN_W::new(self, 31)
    }
}
#[doc = "TIMG_WDTCONFIG0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`wdtconfig0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wdtconfig0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct WDTCONFIG0_SPEC;
impl crate::RegisterSpec for WDTCONFIG0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`wdtconfig0::R`](R) reader structure"]
impl crate::Readable for WDTCONFIG0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`wdtconfig0::W`](W) writer structure"]
impl crate::Writable for WDTCONFIG0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets WDTCONFIG0 to value 0x0004_c000"]
impl crate::Resettable for WDTCONFIG0_SPEC {
    const RESET_VALUE: u32 = 0x0004_c000;
}
