#[doc = "Register `CTRL2` reader"]
pub type R = crate::R<CTRL2_SPEC>;
#[doc = "Register `CTRL2` writer"]
pub type W = crate::W<CTRL2_SPEC>;
#[doc = "Field `MEAS_NUM_LIMIT` reader - enable max meas num"]
pub type MEAS_NUM_LIMIT_R = crate::BitReader;
#[doc = "Field `MEAS_NUM_LIMIT` writer - enable max meas num"]
pub type MEAS_NUM_LIMIT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MAX_MEAS_NUM` reader - max conversion number"]
pub type MAX_MEAS_NUM_R = crate::FieldReader;
#[doc = "Field `MAX_MEAS_NUM` writer - max conversion number"]
pub type MAX_MEAS_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SAR1_INV` reader - 1: data to DIG ADC1 CTRL is inverted, otherwise not"]
pub type SAR1_INV_R = crate::BitReader;
#[doc = "Field `SAR1_INV` writer - 1: data to DIG ADC1 CTRL is inverted, otherwise not"]
pub type SAR1_INV_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAR2_INV` reader - 1: data to DIG ADC2 CTRL is inverted, otherwise not"]
pub type SAR2_INV_R = crate::BitReader;
#[doc = "Field `SAR2_INV` writer - 1: data to DIG ADC2 CTRL is inverted, otherwise not"]
pub type SAR2_INV_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER_TARGET` reader - to set saradc timer target"]
pub type TIMER_TARGET_R = crate::FieldReader<u16>;
#[doc = "Field `TIMER_TARGET` writer - to set saradc timer target"]
pub type TIMER_TARGET_W<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
#[doc = "Field `TIMER_EN` reader - to enable saradc timer trigger"]
pub type TIMER_EN_R = crate::BitReader;
#[doc = "Field `TIMER_EN` writer - to enable saradc timer trigger"]
pub type TIMER_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - enable max meas num"]
    #[inline(always)]
    pub fn meas_num_limit(&self) -> MEAS_NUM_LIMIT_R {
        MEAS_NUM_LIMIT_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:8 - max conversion number"]
    #[inline(always)]
    pub fn max_meas_num(&self) -> MAX_MEAS_NUM_R {
        MAX_MEAS_NUM_R::new(((self.bits >> 1) & 0xff) as u8)
    }
    #[doc = "Bit 9 - 1: data to DIG ADC1 CTRL is inverted, otherwise not"]
    #[inline(always)]
    pub fn sar1_inv(&self) -> SAR1_INV_R {
        SAR1_INV_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - 1: data to DIG ADC2 CTRL is inverted, otherwise not"]
    #[inline(always)]
    pub fn sar2_inv(&self) -> SAR2_INV_R {
        SAR2_INV_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bits 12:23 - to set saradc timer target"]
    #[inline(always)]
    pub fn timer_target(&self) -> TIMER_TARGET_R {
        TIMER_TARGET_R::new(((self.bits >> 12) & 0x0fff) as u16)
    }
    #[doc = "Bit 24 - to enable saradc timer trigger"]
    #[inline(always)]
    pub fn timer_en(&self) -> TIMER_EN_R {
        TIMER_EN_R::new(((self.bits >> 24) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CTRL2")
            .field("meas_num_limit", &self.meas_num_limit())
            .field("max_meas_num", &self.max_meas_num())
            .field("sar1_inv", &self.sar1_inv())
            .field("sar2_inv", &self.sar2_inv())
            .field("timer_target", &self.timer_target())
            .field("timer_en", &self.timer_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - enable max meas num"]
    #[inline(always)]
    pub fn meas_num_limit(&mut self) -> MEAS_NUM_LIMIT_W<'_, CTRL2_SPEC> {
        MEAS_NUM_LIMIT_W::new(self, 0)
    }
    #[doc = "Bits 1:8 - max conversion number"]
    #[inline(always)]
    pub fn max_meas_num(&mut self) -> MAX_MEAS_NUM_W<'_, CTRL2_SPEC> {
        MAX_MEAS_NUM_W::new(self, 1)
    }
    #[doc = "Bit 9 - 1: data to DIG ADC1 CTRL is inverted, otherwise not"]
    #[inline(always)]
    pub fn sar1_inv(&mut self) -> SAR1_INV_W<'_, CTRL2_SPEC> {
        SAR1_INV_W::new(self, 9)
    }
    #[doc = "Bit 10 - 1: data to DIG ADC2 CTRL is inverted, otherwise not"]
    #[inline(always)]
    pub fn sar2_inv(&mut self) -> SAR2_INV_W<'_, CTRL2_SPEC> {
        SAR2_INV_W::new(self, 10)
    }
    #[doc = "Bits 12:23 - to set saradc timer target"]
    #[inline(always)]
    pub fn timer_target(&mut self) -> TIMER_TARGET_W<'_, CTRL2_SPEC> {
        TIMER_TARGET_W::new(self, 12)
    }
    #[doc = "Bit 24 - to enable saradc timer trigger"]
    #[inline(always)]
    pub fn timer_en(&mut self) -> TIMER_EN_W<'_, CTRL2_SPEC> {
        TIMER_EN_W::new(self, 24)
    }
}
#[doc = "digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl2::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl2::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CTRL2_SPEC;
impl crate::RegisterSpec for CTRL2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctrl2::R`](R) reader structure"]
impl crate::Readable for CTRL2_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ctrl2::W`](W) writer structure"]
impl crate::Writable for CTRL2_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CTRL2 to value 0xa1fe"]
impl crate::Resettable for CTRL2_SPEC {
    const RESET_VALUE: u32 = 0xa1fe;
}
