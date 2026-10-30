#[doc = "Register `CTRL_CLK_OUT_EN` reader"]
pub type R = crate::R<CTRL_CLK_OUT_EN_SPEC>;
#[doc = "Register `CTRL_CLK_OUT_EN` writer"]
pub type W = crate::W<CTRL_CLK_OUT_EN_SPEC>;
#[doc = "Field `CLK20_OEN` reader - Set 1 to enable 20m clock"]
pub type CLK20_OEN_R = crate::BitReader;
#[doc = "Field `CLK20_OEN` writer - Set 1 to enable 20m clock"]
pub type CLK20_OEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK22_OEN` reader - Set 1 to enable 22m clock"]
pub type CLK22_OEN_R = crate::BitReader;
#[doc = "Field `CLK22_OEN` writer - Set 1 to enable 22m clock"]
pub type CLK22_OEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK44_OEN` reader - Set 1 to enable 44m clock"]
pub type CLK44_OEN_R = crate::BitReader;
#[doc = "Field `CLK44_OEN` writer - Set 1 to enable 44m clock"]
pub type CLK44_OEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_BB_OEN` reader - Set 1 to enable bb clock"]
pub type CLK_BB_OEN_R = crate::BitReader;
#[doc = "Field `CLK_BB_OEN` writer - Set 1 to enable bb clock"]
pub type CLK_BB_OEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK80_OEN` reader - Set 1 to enable 80m clock"]
pub type CLK80_OEN_R = crate::BitReader;
#[doc = "Field `CLK80_OEN` writer - Set 1 to enable 80m clock"]
pub type CLK80_OEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK160_OEN` reader - Set 1 to enable 160m clock"]
pub type CLK160_OEN_R = crate::BitReader;
#[doc = "Field `CLK160_OEN` writer - Set 1 to enable 160m clock"]
pub type CLK160_OEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_320M_OEN` reader - Set 1 to enable 320m clock"]
pub type CLK_320M_OEN_R = crate::BitReader;
#[doc = "Field `CLK_320M_OEN` writer - Set 1 to enable 320m clock"]
pub type CLK_320M_OEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_ADC_INF_OEN` reader - Reserved"]
pub type CLK_ADC_INF_OEN_R = crate::BitReader;
#[doc = "Field `CLK_ADC_INF_OEN` writer - Reserved"]
pub type CLK_ADC_INF_OEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_DAC_CPU_OEN` reader - Reserved"]
pub type CLK_DAC_CPU_OEN_R = crate::BitReader;
#[doc = "Field `CLK_DAC_CPU_OEN` writer - Reserved"]
pub type CLK_DAC_CPU_OEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK40X_BB_OEN` reader - Set 1 to enable 40x_bb clock"]
pub type CLK40X_BB_OEN_R = crate::BitReader;
#[doc = "Field `CLK40X_BB_OEN` writer - Set 1 to enable 40x_bb clock"]
pub type CLK40X_BB_OEN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_XTAL_OEN` reader - Set 1 to enable xtal clock"]
pub type CLK_XTAL_OEN_R = crate::BitReader;
#[doc = "Field `CLK_XTAL_OEN` writer - Set 1 to enable xtal clock"]
pub type CLK_XTAL_OEN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable 20m clock"]
    #[inline(always)]
    pub fn clk20_oen(&self) -> CLK20_OEN_R {
        CLK20_OEN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 1 to enable 22m clock"]
    #[inline(always)]
    pub fn clk22_oen(&self) -> CLK22_OEN_R {
        CLK22_OEN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set 1 to enable 44m clock"]
    #[inline(always)]
    pub fn clk44_oen(&self) -> CLK44_OEN_R {
        CLK44_OEN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Set 1 to enable bb clock"]
    #[inline(always)]
    pub fn clk_bb_oen(&self) -> CLK_BB_OEN_R {
        CLK_BB_OEN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Set 1 to enable 80m clock"]
    #[inline(always)]
    pub fn clk80_oen(&self) -> CLK80_OEN_R {
        CLK80_OEN_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Set 1 to enable 160m clock"]
    #[inline(always)]
    pub fn clk160_oen(&self) -> CLK160_OEN_R {
        CLK160_OEN_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Set 1 to enable 320m clock"]
    #[inline(always)]
    pub fn clk_320m_oen(&self) -> CLK_320M_OEN_R {
        CLK_320M_OEN_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Reserved"]
    #[inline(always)]
    pub fn clk_adc_inf_oen(&self) -> CLK_ADC_INF_OEN_R {
        CLK_ADC_INF_OEN_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Reserved"]
    #[inline(always)]
    pub fn clk_dac_cpu_oen(&self) -> CLK_DAC_CPU_OEN_R {
        CLK_DAC_CPU_OEN_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Set 1 to enable 40x_bb clock"]
    #[inline(always)]
    pub fn clk40x_bb_oen(&self) -> CLK40X_BB_OEN_R {
        CLK40X_BB_OEN_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Set 1 to enable xtal clock"]
    #[inline(always)]
    pub fn clk_xtal_oen(&self) -> CLK_XTAL_OEN_R {
        CLK_XTAL_OEN_R::new(((self.bits >> 10) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CTRL_CLK_OUT_EN")
            .field("clk20_oen", &self.clk20_oen())
            .field("clk22_oen", &self.clk22_oen())
            .field("clk44_oen", &self.clk44_oen())
            .field("clk_bb_oen", &self.clk_bb_oen())
            .field("clk80_oen", &self.clk80_oen())
            .field("clk160_oen", &self.clk160_oen())
            .field("clk_320m_oen", &self.clk_320m_oen())
            .field("clk_adc_inf_oen", &self.clk_adc_inf_oen())
            .field("clk_dac_cpu_oen", &self.clk_dac_cpu_oen())
            .field("clk40x_bb_oen", &self.clk40x_bb_oen())
            .field("clk_xtal_oen", &self.clk_xtal_oen())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable 20m clock"]
    #[inline(always)]
    pub fn clk20_oen(&mut self) -> CLK20_OEN_W<'_, CTRL_CLK_OUT_EN_SPEC> {
        CLK20_OEN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 1 to enable 22m clock"]
    #[inline(always)]
    pub fn clk22_oen(&mut self) -> CLK22_OEN_W<'_, CTRL_CLK_OUT_EN_SPEC> {
        CLK22_OEN_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set 1 to enable 44m clock"]
    #[inline(always)]
    pub fn clk44_oen(&mut self) -> CLK44_OEN_W<'_, CTRL_CLK_OUT_EN_SPEC> {
        CLK44_OEN_W::new(self, 2)
    }
    #[doc = "Bit 3 - Set 1 to enable bb clock"]
    #[inline(always)]
    pub fn clk_bb_oen(&mut self) -> CLK_BB_OEN_W<'_, CTRL_CLK_OUT_EN_SPEC> {
        CLK_BB_OEN_W::new(self, 3)
    }
    #[doc = "Bit 4 - Set 1 to enable 80m clock"]
    #[inline(always)]
    pub fn clk80_oen(&mut self) -> CLK80_OEN_W<'_, CTRL_CLK_OUT_EN_SPEC> {
        CLK80_OEN_W::new(self, 4)
    }
    #[doc = "Bit 5 - Set 1 to enable 160m clock"]
    #[inline(always)]
    pub fn clk160_oen(&mut self) -> CLK160_OEN_W<'_, CTRL_CLK_OUT_EN_SPEC> {
        CLK160_OEN_W::new(self, 5)
    }
    #[doc = "Bit 6 - Set 1 to enable 320m clock"]
    #[inline(always)]
    pub fn clk_320m_oen(&mut self) -> CLK_320M_OEN_W<'_, CTRL_CLK_OUT_EN_SPEC> {
        CLK_320M_OEN_W::new(self, 6)
    }
    #[doc = "Bit 7 - Reserved"]
    #[inline(always)]
    pub fn clk_adc_inf_oen(&mut self) -> CLK_ADC_INF_OEN_W<'_, CTRL_CLK_OUT_EN_SPEC> {
        CLK_ADC_INF_OEN_W::new(self, 7)
    }
    #[doc = "Bit 8 - Reserved"]
    #[inline(always)]
    pub fn clk_dac_cpu_oen(&mut self) -> CLK_DAC_CPU_OEN_W<'_, CTRL_CLK_OUT_EN_SPEC> {
        CLK_DAC_CPU_OEN_W::new(self, 8)
    }
    #[doc = "Bit 9 - Set 1 to enable 40x_bb clock"]
    #[inline(always)]
    pub fn clk40x_bb_oen(&mut self) -> CLK40X_BB_OEN_W<'_, CTRL_CLK_OUT_EN_SPEC> {
        CLK40X_BB_OEN_W::new(self, 9)
    }
    #[doc = "Bit 10 - Set 1 to enable xtal clock"]
    #[inline(always)]
    pub fn clk_xtal_oen(&mut self) -> CLK_XTAL_OEN_W<'_, CTRL_CLK_OUT_EN_SPEC> {
        CLK_XTAL_OEN_W::new(self, 10)
    }
}
#[doc = "CLK_OUT_EN configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl_clk_out_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl_clk_out_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CTRL_CLK_OUT_EN_SPEC;
impl crate::RegisterSpec for CTRL_CLK_OUT_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctrl_clk_out_en::R`](R) reader structure"]
impl crate::Readable for CTRL_CLK_OUT_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ctrl_clk_out_en::W`](W) writer structure"]
impl crate::Writable for CTRL_CLK_OUT_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CTRL_CLK_OUT_EN to value 0x07ff"]
impl crate::Resettable for CTRL_CLK_OUT_EN_SPEC {
    const RESET_VALUE: u32 = 0x07ff;
}
