#[doc = "Register `RX_CLKM_CONF` reader"]
pub type R = crate::R<RX_CLKM_CONF_SPEC>;
#[doc = "Register `RX_CLKM_CONF` writer"]
pub type W = crate::W<RX_CLKM_CONF_SPEC>;
#[doc = "Field `RX_CLKM_DIV_NUM` reader - Integral I2S clock divider value"]
pub type RX_CLKM_DIV_NUM_R = crate::FieldReader;
#[doc = "Field `RX_CLKM_DIV_NUM` writer - Integral I2S clock divider value"]
pub type RX_CLKM_DIV_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `RX_CLK_ACTIVE` reader - I2S Rx module clock enable signal."]
pub type RX_CLK_ACTIVE_R = crate::BitReader;
#[doc = "Field `RX_CLK_ACTIVE` writer - I2S Rx module clock enable signal."]
pub type RX_CLK_ACTIVE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_CLK_SEL` reader - Select I2S Rx module source clock. 0: no clock. 1: APLL. 2: CLK160. 3: I2S_MCLK_in."]
pub type RX_CLK_SEL_R = crate::FieldReader;
#[doc = "Field `RX_CLK_SEL` writer - Select I2S Rx module source clock. 0: no clock. 1: APLL. 2: CLK160. 3: I2S_MCLK_in."]
pub type RX_CLK_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `MCLK_SEL` reader - 0: UseI2S Tx module clock as I2S_MCLK_OUT. 1: UseI2S Rx module clock as I2S_MCLK_OUT."]
pub type MCLK_SEL_R = crate::BitReader;
#[doc = "Field `MCLK_SEL` writer - 0: UseI2S Tx module clock as I2S_MCLK_OUT. 1: UseI2S Rx module clock as I2S_MCLK_OUT."]
pub type MCLK_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:7 - Integral I2S clock divider value"]
    #[inline(always)]
    pub fn rx_clkm_div_num(&self) -> RX_CLKM_DIV_NUM_R {
        RX_CLKM_DIV_NUM_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bit 26 - I2S Rx module clock enable signal."]
    #[inline(always)]
    pub fn rx_clk_active(&self) -> RX_CLK_ACTIVE_R {
        RX_CLK_ACTIVE_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bits 27:28 - Select I2S Rx module source clock. 0: no clock. 1: APLL. 2: CLK160. 3: I2S_MCLK_in."]
    #[inline(always)]
    pub fn rx_clk_sel(&self) -> RX_CLK_SEL_R {
        RX_CLK_SEL_R::new(((self.bits >> 27) & 3) as u8)
    }
    #[doc = "Bit 29 - 0: UseI2S Tx module clock as I2S_MCLK_OUT. 1: UseI2S Rx module clock as I2S_MCLK_OUT."]
    #[inline(always)]
    pub fn mclk_sel(&self) -> MCLK_SEL_R {
        MCLK_SEL_R::new(((self.bits >> 29) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RX_CLKM_CONF")
            .field("rx_clkm_div_num", &self.rx_clkm_div_num())
            .field("rx_clk_active", &self.rx_clk_active())
            .field("rx_clk_sel", &self.rx_clk_sel())
            .field("mclk_sel", &self.mclk_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - Integral I2S clock divider value"]
    #[inline(always)]
    pub fn rx_clkm_div_num(&mut self) -> RX_CLKM_DIV_NUM_W<'_, RX_CLKM_CONF_SPEC> {
        RX_CLKM_DIV_NUM_W::new(self, 0)
    }
    #[doc = "Bit 26 - I2S Rx module clock enable signal."]
    #[inline(always)]
    pub fn rx_clk_active(&mut self) -> RX_CLK_ACTIVE_W<'_, RX_CLKM_CONF_SPEC> {
        RX_CLK_ACTIVE_W::new(self, 26)
    }
    #[doc = "Bits 27:28 - Select I2S Rx module source clock. 0: no clock. 1: APLL. 2: CLK160. 3: I2S_MCLK_in."]
    #[inline(always)]
    pub fn rx_clk_sel(&mut self) -> RX_CLK_SEL_W<'_, RX_CLKM_CONF_SPEC> {
        RX_CLK_SEL_W::new(self, 27)
    }
    #[doc = "Bit 29 - 0: UseI2S Tx module clock as I2S_MCLK_OUT. 1: UseI2S Rx module clock as I2S_MCLK_OUT."]
    #[inline(always)]
    pub fn mclk_sel(&mut self) -> MCLK_SEL_W<'_, RX_CLKM_CONF_SPEC> {
        MCLK_SEL_W::new(self, 29)
    }
}
#[doc = "I2S RX clock configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_clkm_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_clkm_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RX_CLKM_CONF_SPEC;
impl crate::RegisterSpec for RX_CLKM_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rx_clkm_conf::R`](R) reader structure"]
impl crate::Readable for RX_CLKM_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rx_clkm_conf::W`](W) writer structure"]
impl crate::Writable for RX_CLKM_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RX_CLKM_CONF to value 0x02"]
impl crate::Resettable for RX_CLKM_CONF_SPEC {
    const RESET_VALUE: u32 = 0x02;
}
