#[doc = "Register `CORE_0_PIF_PMS_CONSTRAIN_6` reader"]
pub type R = crate::R<CORE_0_PIF_PMS_CONSTRAIN_6_SPEC>;
#[doc = "Register `CORE_0_PIF_PMS_CONSTRAIN_6` writer"]
pub type W = crate::W<CORE_0_PIF_PMS_CONSTRAIN_6_SPEC>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BT` reader - core_0_pif_pms_constrain_world_1_bt"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BT_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BT` writer - core_0_pif_pms_constrain_world_1_bt"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BT_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2C_EXT0` reader - core_0_pif_pms_constrain_world_1_i2c_ext0"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2C_EXT0_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2C_EXT0` writer - core_0_pif_pms_constrain_world_1_i2c_ext0"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2C_EXT0_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_UHCI0` reader - core_0_pif_pms_constrain_world_1_uhci0"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_UHCI0_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_UHCI0` writer - core_0_pif_pms_constrain_world_1_uhci0"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_UHCI0_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RMT` reader - core_0_pif_pms_constrain_world_1_rmt"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RMT_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RMT` writer - core_0_pif_pms_constrain_world_1_rmt"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RMT_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_LEDC` reader - core_0_pif_pms_constrain_world_1_ledc"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_LEDC_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_LEDC` writer - core_0_pif_pms_constrain_world_1_ledc"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_LEDC_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BB` reader - core_0_pif_pms_constrain_world_1_bb"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BB_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BB` writer - core_0_pif_pms_constrain_world_1_bb"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BB_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP` reader - core_0_pif_pms_constrain_world_1_timergroup"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP` writer - core_0_pif_pms_constrain_world_1_timergroup"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP1` reader - core_0_pif_pms_constrain_world_1_timergroup1"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP1_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP1` writer - core_0_pif_pms_constrain_world_1_timergroup1"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP1_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SYSTIMER` reader - core_0_pif_pms_constrain_world_1_systimer"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SYSTIMER_R = crate::FieldReader;
#[doc = "Field `CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SYSTIMER` writer - core_0_pif_pms_constrain_world_1_systimer"]
pub type CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SYSTIMER_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - core_0_pif_pms_constrain_world_1_bt"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_bt(&self) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BT_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BT_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 4:5 - core_0_pif_pms_constrain_world_1_i2c_ext0"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_i2c_ext0(
        &self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2C_EXT0_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2C_EXT0_R::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bits 6:7 - core_0_pif_pms_constrain_world_1_uhci0"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_uhci0(
        &self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_UHCI0_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_UHCI0_R::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bits 10:11 - core_0_pif_pms_constrain_world_1_rmt"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_rmt(&self) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RMT_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RMT_R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bits 16:17 - core_0_pif_pms_constrain_world_1_ledc"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_ledc(&self) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_LEDC_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_LEDC_R::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 22:23 - core_0_pif_pms_constrain_world_1_bb"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_bb(&self) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BB_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BB_R::new(((self.bits >> 22) & 3) as u8)
    }
    #[doc = "Bits 26:27 - core_0_pif_pms_constrain_world_1_timergroup"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_timergroup(
        &self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP_R::new(((self.bits >> 26) & 3) as u8)
    }
    #[doc = "Bits 28:29 - core_0_pif_pms_constrain_world_1_timergroup1"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_timergroup1(
        &self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP1_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP1_R::new(((self.bits >> 28) & 3) as u8)
    }
    #[doc = "Bits 30:31 - core_0_pif_pms_constrain_world_1_systimer"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_systimer(
        &self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SYSTIMER_R {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SYSTIMER_R::new(((self.bits >> 30) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE_0_PIF_PMS_CONSTRAIN_6")
            .field(
                "core_0_pif_pms_constrain_world_1_bt",
                &self.core_0_pif_pms_constrain_world_1_bt(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_i2c_ext0",
                &self.core_0_pif_pms_constrain_world_1_i2c_ext0(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_uhci0",
                &self.core_0_pif_pms_constrain_world_1_uhci0(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_rmt",
                &self.core_0_pif_pms_constrain_world_1_rmt(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_ledc",
                &self.core_0_pif_pms_constrain_world_1_ledc(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_bb",
                &self.core_0_pif_pms_constrain_world_1_bb(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_timergroup",
                &self.core_0_pif_pms_constrain_world_1_timergroup(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_timergroup1",
                &self.core_0_pif_pms_constrain_world_1_timergroup1(),
            )
            .field(
                "core_0_pif_pms_constrain_world_1_systimer",
                &self.core_0_pif_pms_constrain_world_1_systimer(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - core_0_pif_pms_constrain_world_1_bt"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_bt(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BT_W<'_, CORE_0_PIF_PMS_CONSTRAIN_6_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BT_W::new(self, 0)
    }
    #[doc = "Bits 4:5 - core_0_pif_pms_constrain_world_1_i2c_ext0"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_i2c_ext0(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2C_EXT0_W<'_, CORE_0_PIF_PMS_CONSTRAIN_6_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_I2C_EXT0_W::new(self, 4)
    }
    #[doc = "Bits 6:7 - core_0_pif_pms_constrain_world_1_uhci0"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_uhci0(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_UHCI0_W<'_, CORE_0_PIF_PMS_CONSTRAIN_6_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_UHCI0_W::new(self, 6)
    }
    #[doc = "Bits 10:11 - core_0_pif_pms_constrain_world_1_rmt"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_rmt(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RMT_W<'_, CORE_0_PIF_PMS_CONSTRAIN_6_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_RMT_W::new(self, 10)
    }
    #[doc = "Bits 16:17 - core_0_pif_pms_constrain_world_1_ledc"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_ledc(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_LEDC_W<'_, CORE_0_PIF_PMS_CONSTRAIN_6_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_LEDC_W::new(self, 16)
    }
    #[doc = "Bits 22:23 - core_0_pif_pms_constrain_world_1_bb"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_bb(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BB_W<'_, CORE_0_PIF_PMS_CONSTRAIN_6_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_BB_W::new(self, 22)
    }
    #[doc = "Bits 26:27 - core_0_pif_pms_constrain_world_1_timergroup"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_timergroup(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP_W<'_, CORE_0_PIF_PMS_CONSTRAIN_6_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP_W::new(self, 26)
    }
    #[doc = "Bits 28:29 - core_0_pif_pms_constrain_world_1_timergroup1"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_timergroup1(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP1_W<'_, CORE_0_PIF_PMS_CONSTRAIN_6_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_TIMERGROUP1_W::new(self, 28)
    }
    #[doc = "Bits 30:31 - core_0_pif_pms_constrain_world_1_systimer"]
    #[inline(always)]
    pub fn core_0_pif_pms_constrain_world_1_systimer(
        &mut self,
    ) -> CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SYSTIMER_W<'_, CORE_0_PIF_PMS_CONSTRAIN_6_SPEC> {
        CORE_0_PIF_PMS_CONSTRAIN_WORLD_1_SYSTIMER_W::new(self, 30)
    }
}
#[doc = "SENSITIVE_CORE_0_PIF_PMS_CONSTRAIN_6_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_pif_pms_constrain_6::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_0_pif_pms_constrain_6::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE_0_PIF_PMS_CONSTRAIN_6_SPEC;
impl crate::RegisterSpec for CORE_0_PIF_PMS_CONSTRAIN_6_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core_0_pif_pms_constrain_6::R`](R) reader structure"]
impl crate::Readable for CORE_0_PIF_PMS_CONSTRAIN_6_SPEC {}
#[doc = "`write(|w| ..)` method takes [`core_0_pif_pms_constrain_6::W`](W) writer structure"]
impl crate::Writable for CORE_0_PIF_PMS_CONSTRAIN_6_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CORE_0_PIF_PMS_CONSTRAIN_6 to value 0xfcc3_0cf3"]
impl crate::Resettable for CORE_0_PIF_PMS_CONSTRAIN_6_SPEC {
    const RESET_VALUE: u32 = 0xfcc3_0cf3;
}
