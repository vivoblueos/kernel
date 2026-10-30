#[doc = "Register `BT_LPCK_DIV_FRAC` reader"]
pub type R = crate::R<BT_LPCK_DIV_FRAC_SPEC>;
#[doc = "Register `BT_LPCK_DIV_FRAC` writer"]
pub type W = crate::W<BT_LPCK_DIV_FRAC_SPEC>;
#[doc = "Field `BT_LPCK_DIV_B` reader - reg_bt_lpck_div_b"]
pub type BT_LPCK_DIV_B_R = crate::FieldReader<u16>;
#[doc = "Field `BT_LPCK_DIV_B` writer - reg_bt_lpck_div_b"]
pub type BT_LPCK_DIV_B_W<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
#[doc = "Field `BT_LPCK_DIV_A` reader - reg_bt_lpck_div_a"]
pub type BT_LPCK_DIV_A_R = crate::FieldReader<u16>;
#[doc = "Field `BT_LPCK_DIV_A` writer - reg_bt_lpck_div_a"]
pub type BT_LPCK_DIV_A_W<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
#[doc = "Field `LPCLK_SEL_RTC_SLOW` reader - reg_lpclk_sel_rtc_slow"]
pub type LPCLK_SEL_RTC_SLOW_R = crate::BitReader;
#[doc = "Field `LPCLK_SEL_RTC_SLOW` writer - reg_lpclk_sel_rtc_slow"]
pub type LPCLK_SEL_RTC_SLOW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LPCLK_SEL_8M` reader - reg_lpclk_sel_8m"]
pub type LPCLK_SEL_8M_R = crate::BitReader;
#[doc = "Field `LPCLK_SEL_8M` writer - reg_lpclk_sel_8m"]
pub type LPCLK_SEL_8M_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LPCLK_SEL_XTAL` reader - reg_lpclk_sel_xtal"]
pub type LPCLK_SEL_XTAL_R = crate::BitReader;
#[doc = "Field `LPCLK_SEL_XTAL` writer - reg_lpclk_sel_xtal"]
pub type LPCLK_SEL_XTAL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LPCLK_SEL_XTAL32K` reader - reg_lpclk_sel_xtal32k"]
pub type LPCLK_SEL_XTAL32K_R = crate::BitReader;
#[doc = "Field `LPCLK_SEL_XTAL32K` writer - reg_lpclk_sel_xtal32k"]
pub type LPCLK_SEL_XTAL32K_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LPCLK_RTC_EN` reader - reg_lpclk_rtc_en"]
pub type LPCLK_RTC_EN_R = crate::BitReader;
#[doc = "Field `LPCLK_RTC_EN` writer - reg_lpclk_rtc_en"]
pub type LPCLK_RTC_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:11 - reg_bt_lpck_div_b"]
    #[inline(always)]
    pub fn bt_lpck_div_b(&self) -> BT_LPCK_DIV_B_R {
        BT_LPCK_DIV_B_R::new((self.bits & 0x0fff) as u16)
    }
    #[doc = "Bits 12:23 - reg_bt_lpck_div_a"]
    #[inline(always)]
    pub fn bt_lpck_div_a(&self) -> BT_LPCK_DIV_A_R {
        BT_LPCK_DIV_A_R::new(((self.bits >> 12) & 0x0fff) as u16)
    }
    #[doc = "Bit 24 - reg_lpclk_sel_rtc_slow"]
    #[inline(always)]
    pub fn lpclk_sel_rtc_slow(&self) -> LPCLK_SEL_RTC_SLOW_R {
        LPCLK_SEL_RTC_SLOW_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - reg_lpclk_sel_8m"]
    #[inline(always)]
    pub fn lpclk_sel_8m(&self) -> LPCLK_SEL_8M_R {
        LPCLK_SEL_8M_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - reg_lpclk_sel_xtal"]
    #[inline(always)]
    pub fn lpclk_sel_xtal(&self) -> LPCLK_SEL_XTAL_R {
        LPCLK_SEL_XTAL_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - reg_lpclk_sel_xtal32k"]
    #[inline(always)]
    pub fn lpclk_sel_xtal32k(&self) -> LPCLK_SEL_XTAL32K_R {
        LPCLK_SEL_XTAL32K_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - reg_lpclk_rtc_en"]
    #[inline(always)]
    pub fn lpclk_rtc_en(&self) -> LPCLK_RTC_EN_R {
        LPCLK_RTC_EN_R::new(((self.bits >> 28) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BT_LPCK_DIV_FRAC")
            .field("bt_lpck_div_b", &self.bt_lpck_div_b())
            .field("bt_lpck_div_a", &self.bt_lpck_div_a())
            .field("lpclk_sel_rtc_slow", &self.lpclk_sel_rtc_slow())
            .field("lpclk_sel_8m", &self.lpclk_sel_8m())
            .field("lpclk_sel_xtal", &self.lpclk_sel_xtal())
            .field("lpclk_sel_xtal32k", &self.lpclk_sel_xtal32k())
            .field("lpclk_rtc_en", &self.lpclk_rtc_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:11 - reg_bt_lpck_div_b"]
    #[inline(always)]
    pub fn bt_lpck_div_b(&mut self) -> BT_LPCK_DIV_B_W<'_, BT_LPCK_DIV_FRAC_SPEC> {
        BT_LPCK_DIV_B_W::new(self, 0)
    }
    #[doc = "Bits 12:23 - reg_bt_lpck_div_a"]
    #[inline(always)]
    pub fn bt_lpck_div_a(&mut self) -> BT_LPCK_DIV_A_W<'_, BT_LPCK_DIV_FRAC_SPEC> {
        BT_LPCK_DIV_A_W::new(self, 12)
    }
    #[doc = "Bit 24 - reg_lpclk_sel_rtc_slow"]
    #[inline(always)]
    pub fn lpclk_sel_rtc_slow(&mut self) -> LPCLK_SEL_RTC_SLOW_W<'_, BT_LPCK_DIV_FRAC_SPEC> {
        LPCLK_SEL_RTC_SLOW_W::new(self, 24)
    }
    #[doc = "Bit 25 - reg_lpclk_sel_8m"]
    #[inline(always)]
    pub fn lpclk_sel_8m(&mut self) -> LPCLK_SEL_8M_W<'_, BT_LPCK_DIV_FRAC_SPEC> {
        LPCLK_SEL_8M_W::new(self, 25)
    }
    #[doc = "Bit 26 - reg_lpclk_sel_xtal"]
    #[inline(always)]
    pub fn lpclk_sel_xtal(&mut self) -> LPCLK_SEL_XTAL_W<'_, BT_LPCK_DIV_FRAC_SPEC> {
        LPCLK_SEL_XTAL_W::new(self, 26)
    }
    #[doc = "Bit 27 - reg_lpclk_sel_xtal32k"]
    #[inline(always)]
    pub fn lpclk_sel_xtal32k(&mut self) -> LPCLK_SEL_XTAL32K_W<'_, BT_LPCK_DIV_FRAC_SPEC> {
        LPCLK_SEL_XTAL32K_W::new(self, 27)
    }
    #[doc = "Bit 28 - reg_lpclk_rtc_en"]
    #[inline(always)]
    pub fn lpclk_rtc_en(&mut self) -> LPCLK_RTC_EN_W<'_, BT_LPCK_DIV_FRAC_SPEC> {
        LPCLK_RTC_EN_W::new(self, 28)
    }
}
#[doc = "clock config register\n\nYou can [`read`](crate::Reg::read) this register and get [`bt_lpck_div_frac::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`bt_lpck_div_frac::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BT_LPCK_DIV_FRAC_SPEC;
impl crate::RegisterSpec for BT_LPCK_DIV_FRAC_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`bt_lpck_div_frac::R`](R) reader structure"]
impl crate::Readable for BT_LPCK_DIV_FRAC_SPEC {}
#[doc = "`write(|w| ..)` method takes [`bt_lpck_div_frac::W`](W) writer structure"]
impl crate::Writable for BT_LPCK_DIV_FRAC_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets BT_LPCK_DIV_FRAC to value 0x0200_1001"]
impl crate::Resettable for BT_LPCK_DIV_FRAC_SPEC {
    const RESET_VALUE: u32 = 0x0200_1001;
}
