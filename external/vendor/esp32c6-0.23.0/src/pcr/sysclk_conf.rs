#[doc = "Register `SYSCLK_CONF` reader"]
pub type R = crate::R<SYSCLK_CONF_SPEC>;
#[doc = "Register `SYSCLK_CONF` writer"]
pub type W = crate::W<SYSCLK_CONF_SPEC>;
#[doc = "Field `LS_DIV_NUM` reader - clk_hproot is div1 of low-speed clock-source if clck-source is a low-speed clock-source such as XTAL/FOSC."]
pub type LS_DIV_NUM_R = crate::FieldReader;
#[doc = "Field `HS_DIV_NUM` reader - clk_hproot is div3 of SPLL if the clock-source is high-speed clock SPLL."]
pub type HS_DIV_NUM_R = crate::FieldReader;
#[doc = "Field `SOC_CLK_SEL` reader - This field is used to select clock source. 0: XTAL, 1: SPLL, 2: FOSC, 3: reserved."]
pub type SOC_CLK_SEL_R = crate::FieldReader;
#[doc = "Field `SOC_CLK_SEL` writer - This field is used to select clock source. 0: XTAL, 1: SPLL, 2: FOSC, 3: reserved."]
pub type SOC_CLK_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CLK_XTAL_FREQ` reader - This field indicates the frequency(MHz) of XTAL."]
pub type CLK_XTAL_FREQ_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:7 - clk_hproot is div1 of low-speed clock-source if clck-source is a low-speed clock-source such as XTAL/FOSC."]
    #[inline(always)]
    pub fn ls_div_num(&self) -> LS_DIV_NUM_R {
        LS_DIV_NUM_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - clk_hproot is div3 of SPLL if the clock-source is high-speed clock SPLL."]
    #[inline(always)]
    pub fn hs_div_num(&self) -> HS_DIV_NUM_R {
        HS_DIV_NUM_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:17 - This field is used to select clock source. 0: XTAL, 1: SPLL, 2: FOSC, 3: reserved."]
    #[inline(always)]
    pub fn soc_clk_sel(&self) -> SOC_CLK_SEL_R {
        SOC_CLK_SEL_R::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 24:30 - This field indicates the frequency(MHz) of XTAL."]
    #[inline(always)]
    pub fn clk_xtal_freq(&self) -> CLK_XTAL_FREQ_R {
        CLK_XTAL_FREQ_R::new(((self.bits >> 24) & 0x7f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SYSCLK_CONF")
            .field("ls_div_num", &self.ls_div_num())
            .field("hs_div_num", &self.hs_div_num())
            .field("soc_clk_sel", &self.soc_clk_sel())
            .field("clk_xtal_freq", &self.clk_xtal_freq())
            .finish()
    }
}
impl W {
    #[doc = "Bits 16:17 - This field is used to select clock source. 0: XTAL, 1: SPLL, 2: FOSC, 3: reserved."]
    #[inline(always)]
    pub fn soc_clk_sel(&mut self) -> SOC_CLK_SEL_W<'_, SYSCLK_CONF_SPEC> {
        SOC_CLK_SEL_W::new(self, 16)
    }
}
#[doc = "SYSCLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sysclk_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sysclk_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SYSCLK_CONF_SPEC;
impl crate::RegisterSpec for SYSCLK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sysclk_conf::R`](R) reader structure"]
impl crate::Readable for SYSCLK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sysclk_conf::W`](W) writer structure"]
impl crate::Writable for SYSCLK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SYSCLK_CONF to value 0x2800_0200"]
impl crate::Resettable for SYSCLK_CONF_SPEC {
    const RESET_VALUE: u32 = 0x2800_0200;
}
