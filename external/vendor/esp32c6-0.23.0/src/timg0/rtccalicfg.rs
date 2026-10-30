#[doc = "Register `RTCCALICFG` reader"]
pub type R = crate::R<RTCCALICFG_SPEC>;
#[doc = "Register `RTCCALICFG` writer"]
pub type W = crate::W<RTCCALICFG_SPEC>;
#[doc = "Field `RTC_CALI_START_CYCLING` reader - 0: one-shot frequency calculation,1: periodic frequency calculation,"]
pub type RTC_CALI_START_CYCLING_R = crate::BitReader;
#[doc = "Field `RTC_CALI_START_CYCLING` writer - 0: one-shot frequency calculation,1: periodic frequency calculation,"]
pub type RTC_CALI_START_CYCLING_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RTC_CALI_CLK_SEL` reader - 0:rtc slow clock. 1:clk_8m, 2:xtal_32k."]
pub type RTC_CALI_CLK_SEL_R = crate::FieldReader;
#[doc = "Field `RTC_CALI_CLK_SEL` writer - 0:rtc slow clock. 1:clk_8m, 2:xtal_32k."]
pub type RTC_CALI_CLK_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `RTC_CALI_RDY` reader - indicate one-shot frequency calculation is done."]
pub type RTC_CALI_RDY_R = crate::BitReader;
#[doc = "Field `RTC_CALI_MAX` reader - Configure the time to calculate RTC slow clock's frequency."]
pub type RTC_CALI_MAX_R = crate::FieldReader<u16>;
#[doc = "Field `RTC_CALI_MAX` writer - Configure the time to calculate RTC slow clock's frequency."]
pub type RTC_CALI_MAX_W<'a, REG> = crate::FieldWriter<'a, REG, 15, u16>;
#[doc = "Field `RTC_CALI_START` reader - Set this bit to start one-shot frequency calculation."]
pub type RTC_CALI_START_R = crate::BitReader;
#[doc = "Field `RTC_CALI_START` writer - Set this bit to start one-shot frequency calculation."]
pub type RTC_CALI_START_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 12 - 0: one-shot frequency calculation,1: periodic frequency calculation,"]
    #[inline(always)]
    pub fn rtc_cali_start_cycling(&self) -> RTC_CALI_START_CYCLING_R {
        RTC_CALI_START_CYCLING_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bits 13:14 - 0:rtc slow clock. 1:clk_8m, 2:xtal_32k."]
    #[inline(always)]
    pub fn rtc_cali_clk_sel(&self) -> RTC_CALI_CLK_SEL_R {
        RTC_CALI_CLK_SEL_R::new(((self.bits >> 13) & 3) as u8)
    }
    #[doc = "Bit 15 - indicate one-shot frequency calculation is done."]
    #[inline(always)]
    pub fn rtc_cali_rdy(&self) -> RTC_CALI_RDY_R {
        RTC_CALI_RDY_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 16:30 - Configure the time to calculate RTC slow clock's frequency."]
    #[inline(always)]
    pub fn rtc_cali_max(&self) -> RTC_CALI_MAX_R {
        RTC_CALI_MAX_R::new(((self.bits >> 16) & 0x7fff) as u16)
    }
    #[doc = "Bit 31 - Set this bit to start one-shot frequency calculation."]
    #[inline(always)]
    pub fn rtc_cali_start(&self) -> RTC_CALI_START_R {
        RTC_CALI_START_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RTCCALICFG")
            .field("rtc_cali_start_cycling", &self.rtc_cali_start_cycling())
            .field("rtc_cali_clk_sel", &self.rtc_cali_clk_sel())
            .field("rtc_cali_rdy", &self.rtc_cali_rdy())
            .field("rtc_cali_max", &self.rtc_cali_max())
            .field("rtc_cali_start", &self.rtc_cali_start())
            .finish()
    }
}
impl W {
    #[doc = "Bit 12 - 0: one-shot frequency calculation,1: periodic frequency calculation,"]
    #[inline(always)]
    pub fn rtc_cali_start_cycling(&mut self) -> RTC_CALI_START_CYCLING_W<'_, RTCCALICFG_SPEC> {
        RTC_CALI_START_CYCLING_W::new(self, 12)
    }
    #[doc = "Bits 13:14 - 0:rtc slow clock. 1:clk_8m, 2:xtal_32k."]
    #[inline(always)]
    pub fn rtc_cali_clk_sel(&mut self) -> RTC_CALI_CLK_SEL_W<'_, RTCCALICFG_SPEC> {
        RTC_CALI_CLK_SEL_W::new(self, 13)
    }
    #[doc = "Bits 16:30 - Configure the time to calculate RTC slow clock's frequency."]
    #[inline(always)]
    pub fn rtc_cali_max(&mut self) -> RTC_CALI_MAX_W<'_, RTCCALICFG_SPEC> {
        RTC_CALI_MAX_W::new(self, 16)
    }
    #[doc = "Bit 31 - Set this bit to start one-shot frequency calculation."]
    #[inline(always)]
    pub fn rtc_cali_start(&mut self) -> RTC_CALI_START_W<'_, RTCCALICFG_SPEC> {
        RTC_CALI_START_W::new(self, 31)
    }
}
#[doc = "RTC calibration configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`rtccalicfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rtccalicfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RTCCALICFG_SPEC;
impl crate::RegisterSpec for RTCCALICFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rtccalicfg::R`](R) reader structure"]
impl crate::Readable for RTCCALICFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rtccalicfg::W`](W) writer structure"]
impl crate::Writable for RTCCALICFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RTCCALICFG to value 0x0001_1000"]
impl crate::Resettable for RTCCALICFG_SPEC {
    const RESET_VALUE: u32 = 0x0001_1000;
}
