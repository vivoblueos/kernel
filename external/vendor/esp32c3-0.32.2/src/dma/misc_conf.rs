#[doc = "Register `MISC_CONF` reader"]
pub type R = crate::R<MISC_CONF_SPEC>;
#[doc = "Register `MISC_CONF` writer"]
pub type W = crate::W<MISC_CONF_SPEC>;
#[doc = "Field `AHBM_RST_INTER` reader - Set this bit, then clear this bit to reset the internal ahb FSM."]
pub type AHBM_RST_INTER_R = crate::BitReader;
#[doc = "Field `AHBM_RST_INTER` writer - Set this bit, then clear this bit to reset the internal ahb FSM."]
pub type AHBM_RST_INTER_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ARB_PRI_DIS` reader - Set this bit to disable priority arbitration function."]
pub type ARB_PRI_DIS_R = crate::BitReader;
#[doc = "Field `ARB_PRI_DIS` writer - Set this bit to disable priority arbitration function."]
pub type ARB_PRI_DIS_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_EN` reader - reg_clk_en"]
pub type CLK_EN_R = crate::BitReader;
#[doc = "Field `CLK_EN` writer - reg_clk_en"]
pub type CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set this bit, then clear this bit to reset the internal ahb FSM."]
    #[inline(always)]
    pub fn ahbm_rst_inter(&self) -> AHBM_RST_INTER_R {
        AHBM_RST_INTER_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 2 - Set this bit to disable priority arbitration function."]
    #[inline(always)]
    pub fn arb_pri_dis(&self) -> ARB_PRI_DIS_R {
        ARB_PRI_DIS_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - reg_clk_en"]
    #[inline(always)]
    pub fn clk_en(&self) -> CLK_EN_R {
        CLK_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MISC_CONF")
            .field("ahbm_rst_inter", &self.ahbm_rst_inter())
            .field("arb_pri_dis", &self.arb_pri_dis())
            .field("clk_en", &self.clk_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit, then clear this bit to reset the internal ahb FSM."]
    #[inline(always)]
    pub fn ahbm_rst_inter(&mut self) -> AHBM_RST_INTER_W<'_, MISC_CONF_SPEC> {
        AHBM_RST_INTER_W::new(self, 0)
    }
    #[doc = "Bit 2 - Set this bit to disable priority arbitration function."]
    #[inline(always)]
    pub fn arb_pri_dis(&mut self) -> ARB_PRI_DIS_W<'_, MISC_CONF_SPEC> {
        ARB_PRI_DIS_W::new(self, 2)
    }
    #[doc = "Bit 3 - reg_clk_en"]
    #[inline(always)]
    pub fn clk_en(&mut self) -> CLK_EN_W<'_, MISC_CONF_SPEC> {
        CLK_EN_W::new(self, 3)
    }
}
#[doc = "DMA_MISC_CONF_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`misc_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`misc_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MISC_CONF_SPEC;
impl crate::RegisterSpec for MISC_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`misc_conf::R`](R) reader structure"]
impl crate::Readable for MISC_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`misc_conf::W`](W) writer structure"]
impl crate::Writable for MISC_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MISC_CONF to value 0"]
impl crate::Resettable for MISC_CONF_SPEC {}
