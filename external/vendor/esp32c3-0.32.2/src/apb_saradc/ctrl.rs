#[doc = "Register `CTRL` reader"]
pub type R = crate::R<CTRL_SPEC>;
#[doc = "Register `CTRL` writer"]
pub type W = crate::W<CTRL_SPEC>;
#[doc = "Field `START_FORCE` reader - select software enable saradc sample"]
pub type START_FORCE_R = crate::BitReader;
#[doc = "Field `START_FORCE` writer - select software enable saradc sample"]
pub type START_FORCE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `START` reader - software enable saradc sample"]
pub type START_R = crate::BitReader;
#[doc = "Field `START` writer - software enable saradc sample"]
pub type START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAR_CLK_GATED` reader - SAR clock gated"]
pub type SAR_CLK_GATED_R = crate::BitReader;
#[doc = "Field `SAR_CLK_GATED` writer - SAR clock gated"]
pub type SAR_CLK_GATED_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAR_CLK_DIV` reader - SAR clock divider"]
pub type SAR_CLK_DIV_R = crate::FieldReader;
#[doc = "Field `SAR_CLK_DIV` writer - SAR clock divider"]
pub type SAR_CLK_DIV_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SAR_PATT_LEN` reader - 0 ~ 15 means length 1 ~ 16"]
pub type SAR_PATT_LEN_R = crate::FieldReader;
#[doc = "Field `SAR_PATT_LEN` writer - 0 ~ 15 means length 1 ~ 16"]
pub type SAR_PATT_LEN_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SAR_PATT_P_CLEAR` reader - clear the pointer of pattern table for DIG ADC1 CTRL"]
pub type SAR_PATT_P_CLEAR_R = crate::BitReader;
#[doc = "Field `SAR_PATT_P_CLEAR` writer - clear the pointer of pattern table for DIG ADC1 CTRL"]
pub type SAR_PATT_P_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `XPD_SAR_FORCE` reader - force option to xpd sar blocks"]
pub type XPD_SAR_FORCE_R = crate::FieldReader;
#[doc = "Field `XPD_SAR_FORCE` writer - force option to xpd sar blocks"]
pub type XPD_SAR_FORCE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `WAIT_ARB_CYCLE` reader - wait arbit signal stable after sar_done"]
pub type WAIT_ARB_CYCLE_R = crate::FieldReader;
#[doc = "Field `WAIT_ARB_CYCLE` writer - wait arbit signal stable after sar_done"]
pub type WAIT_ARB_CYCLE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bit 0 - select software enable saradc sample"]
    #[inline(always)]
    pub fn start_force(&self) -> START_FORCE_R {
        START_FORCE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - software enable saradc sample"]
    #[inline(always)]
    pub fn start(&self) -> START_R {
        START_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 6 - SAR clock gated"]
    #[inline(always)]
    pub fn sar_clk_gated(&self) -> SAR_CLK_GATED_R {
        SAR_CLK_GATED_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bits 7:14 - SAR clock divider"]
    #[inline(always)]
    pub fn sar_clk_div(&self) -> SAR_CLK_DIV_R {
        SAR_CLK_DIV_R::new(((self.bits >> 7) & 0xff) as u8)
    }
    #[doc = "Bits 15:17 - 0 ~ 15 means length 1 ~ 16"]
    #[inline(always)]
    pub fn sar_patt_len(&self) -> SAR_PATT_LEN_R {
        SAR_PATT_LEN_R::new(((self.bits >> 15) & 7) as u8)
    }
    #[doc = "Bit 23 - clear the pointer of pattern table for DIG ADC1 CTRL"]
    #[inline(always)]
    pub fn sar_patt_p_clear(&self) -> SAR_PATT_P_CLEAR_R {
        SAR_PATT_P_CLEAR_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bits 27:28 - force option to xpd sar blocks"]
    #[inline(always)]
    pub fn xpd_sar_force(&self) -> XPD_SAR_FORCE_R {
        XPD_SAR_FORCE_R::new(((self.bits >> 27) & 3) as u8)
    }
    #[doc = "Bits 30:31 - wait arbit signal stable after sar_done"]
    #[inline(always)]
    pub fn wait_arb_cycle(&self) -> WAIT_ARB_CYCLE_R {
        WAIT_ARB_CYCLE_R::new(((self.bits >> 30) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CTRL")
            .field("start_force", &self.start_force())
            .field("start", &self.start())
            .field("sar_clk_gated", &self.sar_clk_gated())
            .field("sar_clk_div", &self.sar_clk_div())
            .field("sar_patt_len", &self.sar_patt_len())
            .field("sar_patt_p_clear", &self.sar_patt_p_clear())
            .field("xpd_sar_force", &self.xpd_sar_force())
            .field("wait_arb_cycle", &self.wait_arb_cycle())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - select software enable saradc sample"]
    #[inline(always)]
    pub fn start_force(&mut self) -> START_FORCE_W<'_, CTRL_SPEC> {
        START_FORCE_W::new(self, 0)
    }
    #[doc = "Bit 1 - software enable saradc sample"]
    #[inline(always)]
    pub fn start(&mut self) -> START_W<'_, CTRL_SPEC> {
        START_W::new(self, 1)
    }
    #[doc = "Bit 6 - SAR clock gated"]
    #[inline(always)]
    pub fn sar_clk_gated(&mut self) -> SAR_CLK_GATED_W<'_, CTRL_SPEC> {
        SAR_CLK_GATED_W::new(self, 6)
    }
    #[doc = "Bits 7:14 - SAR clock divider"]
    #[inline(always)]
    pub fn sar_clk_div(&mut self) -> SAR_CLK_DIV_W<'_, CTRL_SPEC> {
        SAR_CLK_DIV_W::new(self, 7)
    }
    #[doc = "Bits 15:17 - 0 ~ 15 means length 1 ~ 16"]
    #[inline(always)]
    pub fn sar_patt_len(&mut self) -> SAR_PATT_LEN_W<'_, CTRL_SPEC> {
        SAR_PATT_LEN_W::new(self, 15)
    }
    #[doc = "Bit 23 - clear the pointer of pattern table for DIG ADC1 CTRL"]
    #[inline(always)]
    pub fn sar_patt_p_clear(&mut self) -> SAR_PATT_P_CLEAR_W<'_, CTRL_SPEC> {
        SAR_PATT_P_CLEAR_W::new(self, 23)
    }
    #[doc = "Bits 27:28 - force option to xpd sar blocks"]
    #[inline(always)]
    pub fn xpd_sar_force(&mut self) -> XPD_SAR_FORCE_W<'_, CTRL_SPEC> {
        XPD_SAR_FORCE_W::new(self, 27)
    }
    #[doc = "Bits 30:31 - wait arbit signal stable after sar_done"]
    #[inline(always)]
    pub fn wait_arb_cycle(&mut self) -> WAIT_ARB_CYCLE_W<'_, CTRL_SPEC> {
        WAIT_ARB_CYCLE_W::new(self, 30)
    }
}
#[doc = "digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CTRL_SPEC;
impl crate::RegisterSpec for CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctrl::R`](R) reader structure"]
impl crate::Readable for CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ctrl::W`](W) writer structure"]
impl crate::Writable for CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CTRL to value 0x4003_8240"]
impl crate::Resettable for CTRL_SPEC {
    const RESET_VALUE: u32 = 0x4003_8240;
}
