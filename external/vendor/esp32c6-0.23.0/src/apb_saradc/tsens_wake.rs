#[doc = "Register `TSENS_WAKE` reader"]
pub type R = crate::R<TSENS_WAKE_SPEC>;
#[doc = "Register `TSENS_WAKE` writer"]
pub type W = crate::W<TSENS_WAKE_SPEC>;
#[doc = "Field `WAKEUP_TH_LOW` reader - reg_wakeup_th_low"]
pub type WAKEUP_TH_LOW_R = crate::FieldReader;
#[doc = "Field `WAKEUP_TH_LOW` writer - reg_wakeup_th_low"]
pub type WAKEUP_TH_LOW_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `WAKEUP_TH_HIGH` reader - reg_wakeup_th_high"]
pub type WAKEUP_TH_HIGH_R = crate::FieldReader;
#[doc = "Field `WAKEUP_TH_HIGH` writer - reg_wakeup_th_high"]
pub type WAKEUP_TH_HIGH_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `WAKEUP_OVER_UPPER_TH` reader - reg_wakeup_over_upper_th"]
pub type WAKEUP_OVER_UPPER_TH_R = crate::BitReader;
#[doc = "Field `WAKEUP_MODE` reader - reg_wakeup_mode"]
pub type WAKEUP_MODE_R = crate::BitReader;
#[doc = "Field `WAKEUP_MODE` writer - reg_wakeup_mode"]
pub type WAKEUP_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WAKEUP_EN` reader - reg_wakeup_en"]
pub type WAKEUP_EN_R = crate::BitReader;
#[doc = "Field `WAKEUP_EN` writer - reg_wakeup_en"]
pub type WAKEUP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:7 - reg_wakeup_th_low"]
    #[inline(always)]
    pub fn wakeup_th_low(&self) -> WAKEUP_TH_LOW_R {
        WAKEUP_TH_LOW_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - reg_wakeup_th_high"]
    #[inline(always)]
    pub fn wakeup_th_high(&self) -> WAKEUP_TH_HIGH_R {
        WAKEUP_TH_HIGH_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bit 16 - reg_wakeup_over_upper_th"]
    #[inline(always)]
    pub fn wakeup_over_upper_th(&self) -> WAKEUP_OVER_UPPER_TH_R {
        WAKEUP_OVER_UPPER_TH_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - reg_wakeup_mode"]
    #[inline(always)]
    pub fn wakeup_mode(&self) -> WAKEUP_MODE_R {
        WAKEUP_MODE_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - reg_wakeup_en"]
    #[inline(always)]
    pub fn wakeup_en(&self) -> WAKEUP_EN_R {
        WAKEUP_EN_R::new(((self.bits >> 18) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TSENS_WAKE")
            .field("wakeup_th_low", &self.wakeup_th_low())
            .field("wakeup_th_high", &self.wakeup_th_high())
            .field("wakeup_over_upper_th", &self.wakeup_over_upper_th())
            .field("wakeup_mode", &self.wakeup_mode())
            .field("wakeup_en", &self.wakeup_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - reg_wakeup_th_low"]
    #[inline(always)]
    pub fn wakeup_th_low(&mut self) -> WAKEUP_TH_LOW_W<'_, TSENS_WAKE_SPEC> {
        WAKEUP_TH_LOW_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - reg_wakeup_th_high"]
    #[inline(always)]
    pub fn wakeup_th_high(&mut self) -> WAKEUP_TH_HIGH_W<'_, TSENS_WAKE_SPEC> {
        WAKEUP_TH_HIGH_W::new(self, 8)
    }
    #[doc = "Bit 17 - reg_wakeup_mode"]
    #[inline(always)]
    pub fn wakeup_mode(&mut self) -> WAKEUP_MODE_W<'_, TSENS_WAKE_SPEC> {
        WAKEUP_MODE_W::new(self, 17)
    }
    #[doc = "Bit 18 - reg_wakeup_en"]
    #[inline(always)]
    pub fn wakeup_en(&mut self) -> WAKEUP_EN_W<'_, TSENS_WAKE_SPEC> {
        WAKEUP_EN_W::new(self, 18)
    }
}
#[doc = "digital tsens configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`tsens_wake::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tsens_wake::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TSENS_WAKE_SPEC;
impl crate::RegisterSpec for TSENS_WAKE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tsens_wake::R`](R) reader structure"]
impl crate::Readable for TSENS_WAKE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tsens_wake::W`](W) writer structure"]
impl crate::Writable for TSENS_WAKE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TSENS_WAKE to value 0xff00"]
impl crate::Resettable for TSENS_WAKE_SPEC {
    const RESET_VALUE: u32 = 0xff00;
}
