#[doc = "Register `CLKM_CONF` reader"]
pub type R = crate::R<CLKM_CONF_SPEC>;
#[doc = "Register `CLKM_CONF` writer"]
pub type W = crate::W<CLKM_CONF_SPEC>;
#[doc = "Field `CLKM_DIV_NUM` reader - Integral I2S clock divider value"]
pub type CLKM_DIV_NUM_R = crate::FieldReader;
#[doc = "Field `CLKM_DIV_NUM` writer - Integral I2S clock divider value"]
pub type CLKM_DIV_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `CLKM_DIV_B` reader - Fractional clock divider numerator value"]
pub type CLKM_DIV_B_R = crate::FieldReader;
#[doc = "Field `CLKM_DIV_B` writer - Fractional clock divider numerator value"]
pub type CLKM_DIV_B_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `CLKM_DIV_A` reader - Fractional clock divider denominator value"]
pub type CLKM_DIV_A_R = crate::FieldReader;
#[doc = "Field `CLKM_DIV_A` writer - Fractional clock divider denominator value"]
pub type CLKM_DIV_A_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `CLK_EN` reader - reg clk en"]
pub type CLK_EN_R = crate::BitReader;
#[doc = "Field `CLK_EN` writer - reg clk en"]
pub type CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_SEL` reader - Set this bit to enable clk_apll"]
pub type CLK_SEL_R = crate::FieldReader;
#[doc = "Field `CLK_SEL` writer - Set this bit to enable clk_apll"]
pub type CLK_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:7 - Integral I2S clock divider value"]
    #[inline(always)]
    pub fn clkm_div_num(&self) -> CLKM_DIV_NUM_R {
        CLKM_DIV_NUM_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:13 - Fractional clock divider numerator value"]
    #[inline(always)]
    pub fn clkm_div_b(&self) -> CLKM_DIV_B_R {
        CLKM_DIV_B_R::new(((self.bits >> 8) & 0x3f) as u8)
    }
    #[doc = "Bits 14:19 - Fractional clock divider denominator value"]
    #[inline(always)]
    pub fn clkm_div_a(&self) -> CLKM_DIV_A_R {
        CLKM_DIV_A_R::new(((self.bits >> 14) & 0x3f) as u8)
    }
    #[doc = "Bit 20 - reg clk en"]
    #[inline(always)]
    pub fn clk_en(&self) -> CLK_EN_R {
        CLK_EN_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bits 21:22 - Set this bit to enable clk_apll"]
    #[inline(always)]
    pub fn clk_sel(&self) -> CLK_SEL_R {
        CLK_SEL_R::new(((self.bits >> 21) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLKM_CONF")
            .field("clkm_div_num", &self.clkm_div_num())
            .field("clkm_div_b", &self.clkm_div_b())
            .field("clkm_div_a", &self.clkm_div_a())
            .field("clk_en", &self.clk_en())
            .field("clk_sel", &self.clk_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - Integral I2S clock divider value"]
    #[inline(always)]
    pub fn clkm_div_num(&mut self) -> CLKM_DIV_NUM_W<'_, CLKM_CONF_SPEC> {
        CLKM_DIV_NUM_W::new(self, 0)
    }
    #[doc = "Bits 8:13 - Fractional clock divider numerator value"]
    #[inline(always)]
    pub fn clkm_div_b(&mut self) -> CLKM_DIV_B_W<'_, CLKM_CONF_SPEC> {
        CLKM_DIV_B_W::new(self, 8)
    }
    #[doc = "Bits 14:19 - Fractional clock divider denominator value"]
    #[inline(always)]
    pub fn clkm_div_a(&mut self) -> CLKM_DIV_A_W<'_, CLKM_CONF_SPEC> {
        CLKM_DIV_A_W::new(self, 14)
    }
    #[doc = "Bit 20 - reg clk en"]
    #[inline(always)]
    pub fn clk_en(&mut self) -> CLK_EN_W<'_, CLKM_CONF_SPEC> {
        CLK_EN_W::new(self, 20)
    }
    #[doc = "Bits 21:22 - Set this bit to enable clk_apll"]
    #[inline(always)]
    pub fn clk_sel(&mut self) -> CLK_SEL_W<'_, CLKM_CONF_SPEC> {
        CLK_SEL_W::new(self, 21)
    }
}
#[doc = "digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`clkm_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clkm_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLKM_CONF_SPEC;
impl crate::RegisterSpec for CLKM_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clkm_conf::R`](R) reader structure"]
impl crate::Readable for CLKM_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clkm_conf::W`](W) writer structure"]
impl crate::Writable for CLKM_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLKM_CONF to value 0x04"]
impl crate::Resettable for CLKM_CONF_SPEC {
    const RESET_VALUE: u32 = 0x04;
}
