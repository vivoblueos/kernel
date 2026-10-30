#[doc = "Register `LP_SLEEP_LP_CK_POWER` reader"]
pub type R = crate::R<LP_SLEEP_LP_CK_POWER_SPEC>;
#[doc = "Register `LP_SLEEP_LP_CK_POWER` writer"]
pub type W = crate::W<LP_SLEEP_LP_CK_POWER_SPEC>;
#[doc = "Field `LP_SLEEP_XPD_XTAL32K` reader - need_des"]
pub type LP_SLEEP_XPD_XTAL32K_R = crate::BitReader;
#[doc = "Field `LP_SLEEP_XPD_XTAL32K` writer - need_des"]
pub type LP_SLEEP_XPD_XTAL32K_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_SLEEP_XPD_RC32K` reader - need_des"]
pub type LP_SLEEP_XPD_RC32K_R = crate::BitReader;
#[doc = "Field `LP_SLEEP_XPD_RC32K` writer - need_des"]
pub type LP_SLEEP_XPD_RC32K_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_SLEEP_XPD_FOSC_CLK` reader - need_des"]
pub type LP_SLEEP_XPD_FOSC_CLK_R = crate::BitReader;
#[doc = "Field `LP_SLEEP_XPD_FOSC_CLK` writer - need_des"]
pub type LP_SLEEP_XPD_FOSC_CLK_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_SLEEP_PD_OSC_CLK` reader - need_des"]
pub type LP_SLEEP_PD_OSC_CLK_R = crate::BitReader;
#[doc = "Field `LP_SLEEP_PD_OSC_CLK` writer - need_des"]
pub type LP_SLEEP_PD_OSC_CLK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn lp_sleep_xpd_xtal32k(&self) -> LP_SLEEP_XPD_XTAL32K_R {
        LP_SLEEP_XPD_XTAL32K_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn lp_sleep_xpd_rc32k(&self) -> LP_SLEEP_XPD_RC32K_R {
        LP_SLEEP_XPD_RC32K_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn lp_sleep_xpd_fosc_clk(&self) -> LP_SLEEP_XPD_FOSC_CLK_R {
        LP_SLEEP_XPD_FOSC_CLK_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lp_sleep_pd_osc_clk(&self) -> LP_SLEEP_PD_OSC_CLK_R {
        LP_SLEEP_PD_OSC_CLK_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LP_SLEEP_LP_CK_POWER")
            .field("lp_sleep_xpd_xtal32k", &self.lp_sleep_xpd_xtal32k())
            .field("lp_sleep_xpd_rc32k", &self.lp_sleep_xpd_rc32k())
            .field("lp_sleep_xpd_fosc_clk", &self.lp_sleep_xpd_fosc_clk())
            .field("lp_sleep_pd_osc_clk", &self.lp_sleep_pd_osc_clk())
            .finish()
    }
}
impl W {
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn lp_sleep_xpd_xtal32k(
        &mut self,
    ) -> LP_SLEEP_XPD_XTAL32K_W<'_, LP_SLEEP_LP_CK_POWER_SPEC> {
        LP_SLEEP_XPD_XTAL32K_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn lp_sleep_xpd_rc32k(&mut self) -> LP_SLEEP_XPD_RC32K_W<'_, LP_SLEEP_LP_CK_POWER_SPEC> {
        LP_SLEEP_XPD_RC32K_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn lp_sleep_xpd_fosc_clk(
        &mut self,
    ) -> LP_SLEEP_XPD_FOSC_CLK_W<'_, LP_SLEEP_LP_CK_POWER_SPEC> {
        LP_SLEEP_XPD_FOSC_CLK_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lp_sleep_pd_osc_clk(&mut self) -> LP_SLEEP_PD_OSC_CLK_W<'_, LP_SLEEP_LP_CK_POWER_SPEC> {
        LP_SLEEP_PD_OSC_CLK_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`lp_sleep_lp_ck_power::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lp_sleep_lp_ck_power::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LP_SLEEP_LP_CK_POWER_SPEC;
impl crate::RegisterSpec for LP_SLEEP_LP_CK_POWER_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lp_sleep_lp_ck_power::R`](R) reader structure"]
impl crate::Readable for LP_SLEEP_LP_CK_POWER_SPEC {}
#[doc = "`write(|w| ..)` method takes [`lp_sleep_lp_ck_power::W`](W) writer structure"]
impl crate::Writable for LP_SLEEP_LP_CK_POWER_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LP_SLEEP_LP_CK_POWER to value 0x4000_0000"]
impl crate::Resettable for LP_SLEEP_LP_CK_POWER_SPEC {
    const RESET_VALUE: u32 = 0x4000_0000;
}
