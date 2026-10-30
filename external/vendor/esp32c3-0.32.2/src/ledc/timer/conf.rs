#[doc = "Register `CONF` reader"]
pub type R = crate::R<CONF_SPEC>;
#[doc = "Register `CONF` writer"]
pub type W = crate::W<CONF_SPEC>;
#[doc = "Field `DUTY_RES` reader - reg_lstimer0_duty_res."]
pub type DUTY_RES_R = crate::FieldReader;
#[doc = "Field `DUTY_RES` writer - reg_lstimer0_duty_res."]
pub type DUTY_RES_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CLK_DIV` reader - reg_clk_div_lstimer0."]
pub type CLK_DIV_R = crate::FieldReader<u32>;
#[doc = "Field `CLK_DIV` writer - reg_clk_div_lstimer0."]
pub type CLK_DIV_W<'a, REG> = crate::FieldWriter<'a, REG, 18, u32>;
#[doc = "Field `PAUSE` reader - reg_lstimer0_pause."]
pub type PAUSE_R = crate::BitReader;
#[doc = "Field `PAUSE` writer - reg_lstimer0_pause."]
pub type PAUSE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST` reader - reg_lstimer0_rst."]
pub type RST_R = crate::BitReader;
#[doc = "Field `RST` writer - reg_lstimer0_rst."]
pub type RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TICK_SEL` reader - reg_tick_sel_lstimer0."]
pub type TICK_SEL_R = crate::BitReader;
#[doc = "Field `TICK_SEL` writer - reg_tick_sel_lstimer0."]
pub type TICK_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PARA_UP` writer - reg_lstimer0_para_up."]
pub type PARA_UP_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:3 - reg_lstimer0_duty_res."]
    #[inline(always)]
    pub fn duty_res(&self) -> DUTY_RES_R {
        DUTY_RES_R::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:21 - reg_clk_div_lstimer0."]
    #[inline(always)]
    pub fn clk_div(&self) -> CLK_DIV_R {
        CLK_DIV_R::new((self.bits >> 4) & 0x0003_ffff)
    }
    #[doc = "Bit 22 - reg_lstimer0_pause."]
    #[inline(always)]
    pub fn pause(&self) -> PAUSE_R {
        PAUSE_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - reg_lstimer0_rst."]
    #[inline(always)]
    pub fn rst(&self) -> RST_R {
        RST_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - reg_tick_sel_lstimer0."]
    #[inline(always)]
    pub fn tick_sel(&self) -> TICK_SEL_R {
        TICK_SEL_R::new(((self.bits >> 24) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF")
            .field("duty_res", &self.duty_res())
            .field("clk_div", &self.clk_div())
            .field("pause", &self.pause())
            .field("rst", &self.rst())
            .field("tick_sel", &self.tick_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3 - reg_lstimer0_duty_res."]
    #[inline(always)]
    pub fn duty_res(&mut self) -> DUTY_RES_W<'_, CONF_SPEC> {
        DUTY_RES_W::new(self, 0)
    }
    #[doc = "Bits 4:21 - reg_clk_div_lstimer0."]
    #[inline(always)]
    pub fn clk_div(&mut self) -> CLK_DIV_W<'_, CONF_SPEC> {
        CLK_DIV_W::new(self, 4)
    }
    #[doc = "Bit 22 - reg_lstimer0_pause."]
    #[inline(always)]
    pub fn pause(&mut self) -> PAUSE_W<'_, CONF_SPEC> {
        PAUSE_W::new(self, 22)
    }
    #[doc = "Bit 23 - reg_lstimer0_rst."]
    #[inline(always)]
    pub fn rst(&mut self) -> RST_W<'_, CONF_SPEC> {
        RST_W::new(self, 23)
    }
    #[doc = "Bit 24 - reg_tick_sel_lstimer0."]
    #[inline(always)]
    pub fn tick_sel(&mut self) -> TICK_SEL_W<'_, CONF_SPEC> {
        TICK_SEL_W::new(self, 24)
    }
    #[doc = "Bit 25 - reg_lstimer0_para_up."]
    #[inline(always)]
    pub fn para_up(&mut self) -> PARA_UP_W<'_, CONF_SPEC> {
        PARA_UP_W::new(self, 25)
    }
}
#[doc = "LEDC_LSTIMER0_CONF.\n\nYou can [`read`](crate::Reg::read) this register and get [`conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF_SPEC;
impl crate::RegisterSpec for CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf::R`](R) reader structure"]
impl crate::Readable for CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf::W`](W) writer structure"]
impl crate::Writable for CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF to value 0x0080_0000"]
impl crate::Resettable for CONF_SPEC {
    const RESET_VALUE: u32 = 0x0080_0000;
}
