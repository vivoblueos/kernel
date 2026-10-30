#[doc = "Register `RTC_CNTL` reader"]
pub type R = crate::R<RTC_CNTL_SPEC>;
#[doc = "Register `RTC_CNTL` writer"]
pub type W = crate::W<RTC_CNTL_SPEC>;
#[doc = "Field `DIG_REG_CAL_EN` reader - software enable digital regulator cali"]
pub type DIG_REG_CAL_EN_R = crate::BitReader;
#[doc = "Field `DIG_REG_CAL_EN` writer - software enable digital regulator cali"]
pub type DIG_REG_CAL_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SCK_DCAP` reader - SCK_DCAP"]
pub type SCK_DCAP_R = crate::FieldReader;
#[doc = "Field `SCK_DCAP` writer - SCK_DCAP"]
pub type SCK_DCAP_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `DBOOST_FORCE_PD` reader - RTC_DBOOST force power down"]
pub type DBOOST_FORCE_PD_R = crate::BitReader;
#[doc = "Field `DBOOST_FORCE_PD` writer - RTC_DBOOST force power down"]
pub type DBOOST_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DBOOST_FORCE_PU` reader - RTC_DBOOST force power up"]
pub type DBOOST_FORCE_PU_R = crate::BitReader;
#[doc = "Field `DBOOST_FORCE_PU` writer - RTC_DBOOST force power up"]
pub type DBOOST_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `REGULATOR_FORCE_PD` reader - RTC_REG force power down (for RTC_REG power down means decrease the voltage to 0.8v or lower )"]
pub type REGULATOR_FORCE_PD_R = crate::BitReader;
#[doc = "Field `REGULATOR_FORCE_PD` writer - RTC_REG force power down (for RTC_REG power down means decrease the voltage to 0.8v or lower )"]
pub type REGULATOR_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `REGULATOR_FORCE_PU` reader - RTC_REG force power up"]
pub type REGULATOR_FORCE_PU_R = crate::BitReader;
#[doc = "Field `REGULATOR_FORCE_PU` writer - RTC_REG force power up"]
pub type REGULATOR_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 7 - software enable digital regulator cali"]
    #[inline(always)]
    pub fn dig_reg_cal_en(&self) -> DIG_REG_CAL_EN_R {
        DIG_REG_CAL_EN_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 14:21 - SCK_DCAP"]
    #[inline(always)]
    pub fn sck_dcap(&self) -> SCK_DCAP_R {
        SCK_DCAP_R::new(((self.bits >> 14) & 0xff) as u8)
    }
    #[doc = "Bit 28 - RTC_DBOOST force power down"]
    #[inline(always)]
    pub fn dboost_force_pd(&self) -> DBOOST_FORCE_PD_R {
        DBOOST_FORCE_PD_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - RTC_DBOOST force power up"]
    #[inline(always)]
    pub fn dboost_force_pu(&self) -> DBOOST_FORCE_PU_R {
        DBOOST_FORCE_PU_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - RTC_REG force power down (for RTC_REG power down means decrease the voltage to 0.8v or lower )"]
    #[inline(always)]
    pub fn regulator_force_pd(&self) -> REGULATOR_FORCE_PD_R {
        REGULATOR_FORCE_PD_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - RTC_REG force power up"]
    #[inline(always)]
    pub fn regulator_force_pu(&self) -> REGULATOR_FORCE_PU_R {
        REGULATOR_FORCE_PU_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RTC_CNTL")
            .field("dig_reg_cal_en", &self.dig_reg_cal_en())
            .field("sck_dcap", &self.sck_dcap())
            .field("dboost_force_pd", &self.dboost_force_pd())
            .field("dboost_force_pu", &self.dboost_force_pu())
            .field("regulator_force_pd", &self.regulator_force_pd())
            .field("regulator_force_pu", &self.regulator_force_pu())
            .finish()
    }
}
impl W {
    #[doc = "Bit 7 - software enable digital regulator cali"]
    #[inline(always)]
    pub fn dig_reg_cal_en(&mut self) -> DIG_REG_CAL_EN_W<'_, RTC_CNTL_SPEC> {
        DIG_REG_CAL_EN_W::new(self, 7)
    }
    #[doc = "Bits 14:21 - SCK_DCAP"]
    #[inline(always)]
    pub fn sck_dcap(&mut self) -> SCK_DCAP_W<'_, RTC_CNTL_SPEC> {
        SCK_DCAP_W::new(self, 14)
    }
    #[doc = "Bit 28 - RTC_DBOOST force power down"]
    #[inline(always)]
    pub fn dboost_force_pd(&mut self) -> DBOOST_FORCE_PD_W<'_, RTC_CNTL_SPEC> {
        DBOOST_FORCE_PD_W::new(self, 28)
    }
    #[doc = "Bit 29 - RTC_DBOOST force power up"]
    #[inline(always)]
    pub fn dboost_force_pu(&mut self) -> DBOOST_FORCE_PU_W<'_, RTC_CNTL_SPEC> {
        DBOOST_FORCE_PU_W::new(self, 29)
    }
    #[doc = "Bit 30 - RTC_REG force power down (for RTC_REG power down means decrease the voltage to 0.8v or lower )"]
    #[inline(always)]
    pub fn regulator_force_pd(&mut self) -> REGULATOR_FORCE_PD_W<'_, RTC_CNTL_SPEC> {
        REGULATOR_FORCE_PD_W::new(self, 30)
    }
    #[doc = "Bit 31 - RTC_REG force power up"]
    #[inline(always)]
    pub fn regulator_force_pu(&mut self) -> REGULATOR_FORCE_PU_W<'_, RTC_CNTL_SPEC> {
        REGULATOR_FORCE_PU_W::new(self, 31)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`rtc_cntl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rtc_cntl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RTC_CNTL_SPEC;
impl crate::RegisterSpec for RTC_CNTL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rtc_cntl::R`](R) reader structure"]
impl crate::Readable for RTC_CNTL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rtc_cntl::W`](W) writer structure"]
impl crate::Writable for RTC_CNTL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RTC_CNTL to value 0xa000_0000"]
impl crate::Resettable for RTC_CNTL_SPEC {
    const RESET_VALUE: u32 = 0xa000_0000;
}
