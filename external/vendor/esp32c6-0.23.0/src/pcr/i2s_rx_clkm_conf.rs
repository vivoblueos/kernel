#[doc = "Register `I2S_RX_CLKM_CONF` reader"]
pub type R = crate::R<I2S_RX_CLKM_CONF_SPEC>;
#[doc = "Register `I2S_RX_CLKM_CONF` writer"]
pub type W = crate::W<I2S_RX_CLKM_CONF_SPEC>;
#[doc = "Field `I2S_RX_CLKM_DIV_NUM` reader - Integral I2S clock divider value"]
pub type I2S_RX_CLKM_DIV_NUM_R = crate::FieldReader;
#[doc = "Field `I2S_RX_CLKM_DIV_NUM` writer - Integral I2S clock divider value"]
pub type I2S_RX_CLKM_DIV_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `I2S_RX_CLKM_SEL` reader - Select I2S Rx module source clock. 0: no clock. 1: APLL. 2: CLK160. 3: I2S_MCLK_in."]
pub type I2S_RX_CLKM_SEL_R = crate::FieldReader;
#[doc = "Field `I2S_RX_CLKM_SEL` writer - Select I2S Rx module source clock. 0: no clock. 1: APLL. 2: CLK160. 3: I2S_MCLK_in."]
pub type I2S_RX_CLKM_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `I2S_RX_CLKM_EN` reader - Set 1 to enable i2s_rx function clock"]
pub type I2S_RX_CLKM_EN_R = crate::BitReader;
#[doc = "Field `I2S_RX_CLKM_EN` writer - Set 1 to enable i2s_rx function clock"]
pub type I2S_RX_CLKM_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2S_MCLK_SEL` reader - This field is used to select master-clock. 0(default): clk_i2s_rx, 1: clk_i2s_tx"]
pub type I2S_MCLK_SEL_R = crate::BitReader;
#[doc = "Field `I2S_MCLK_SEL` writer - This field is used to select master-clock. 0(default): clk_i2s_rx, 1: clk_i2s_tx"]
pub type I2S_MCLK_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 12:19 - Integral I2S clock divider value"]
    #[inline(always)]
    pub fn i2s_rx_clkm_div_num(&self) -> I2S_RX_CLKM_DIV_NUM_R {
        I2S_RX_CLKM_DIV_NUM_R::new(((self.bits >> 12) & 0xff) as u8)
    }
    #[doc = "Bits 20:21 - Select I2S Rx module source clock. 0: no clock. 1: APLL. 2: CLK160. 3: I2S_MCLK_in."]
    #[inline(always)]
    pub fn i2s_rx_clkm_sel(&self) -> I2S_RX_CLKM_SEL_R {
        I2S_RX_CLKM_SEL_R::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bit 22 - Set 1 to enable i2s_rx function clock"]
    #[inline(always)]
    pub fn i2s_rx_clkm_en(&self) -> I2S_RX_CLKM_EN_R {
        I2S_RX_CLKM_EN_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - This field is used to select master-clock. 0(default): clk_i2s_rx, 1: clk_i2s_tx"]
    #[inline(always)]
    pub fn i2s_mclk_sel(&self) -> I2S_MCLK_SEL_R {
        I2S_MCLK_SEL_R::new(((self.bits >> 23) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("I2S_RX_CLKM_CONF")
            .field("i2s_rx_clkm_div_num", &self.i2s_rx_clkm_div_num())
            .field("i2s_rx_clkm_sel", &self.i2s_rx_clkm_sel())
            .field("i2s_rx_clkm_en", &self.i2s_rx_clkm_en())
            .field("i2s_mclk_sel", &self.i2s_mclk_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 12:19 - Integral I2S clock divider value"]
    #[inline(always)]
    pub fn i2s_rx_clkm_div_num(&mut self) -> I2S_RX_CLKM_DIV_NUM_W<'_, I2S_RX_CLKM_CONF_SPEC> {
        I2S_RX_CLKM_DIV_NUM_W::new(self, 12)
    }
    #[doc = "Bits 20:21 - Select I2S Rx module source clock. 0: no clock. 1: APLL. 2: CLK160. 3: I2S_MCLK_in."]
    #[inline(always)]
    pub fn i2s_rx_clkm_sel(&mut self) -> I2S_RX_CLKM_SEL_W<'_, I2S_RX_CLKM_CONF_SPEC> {
        I2S_RX_CLKM_SEL_W::new(self, 20)
    }
    #[doc = "Bit 22 - Set 1 to enable i2s_rx function clock"]
    #[inline(always)]
    pub fn i2s_rx_clkm_en(&mut self) -> I2S_RX_CLKM_EN_W<'_, I2S_RX_CLKM_CONF_SPEC> {
        I2S_RX_CLKM_EN_W::new(self, 22)
    }
    #[doc = "Bit 23 - This field is used to select master-clock. 0(default): clk_i2s_rx, 1: clk_i2s_tx"]
    #[inline(always)]
    pub fn i2s_mclk_sel(&mut self) -> I2S_MCLK_SEL_W<'_, I2S_RX_CLKM_CONF_SPEC> {
        I2S_MCLK_SEL_W::new(self, 23)
    }
}
#[doc = "I2S_RX_CLKM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2s_rx_clkm_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2s_rx_clkm_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct I2S_RX_CLKM_CONF_SPEC;
impl crate::RegisterSpec for I2S_RX_CLKM_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`i2s_rx_clkm_conf::R`](R) reader structure"]
impl crate::Readable for I2S_RX_CLKM_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`i2s_rx_clkm_conf::W`](W) writer structure"]
impl crate::Writable for I2S_RX_CLKM_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets I2S_RX_CLKM_CONF to value 0x0040_2000"]
impl crate::Resettable for I2S_RX_CLKM_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0040_2000;
}
