#[doc = "Register `IOMUX_CLK_CONF` reader"]
pub type R = crate::R<IOMUX_CLK_CONF_SPEC>;
#[doc = "Register `IOMUX_CLK_CONF` writer"]
pub type W = crate::W<IOMUX_CLK_CONF_SPEC>;
#[doc = "Field `IOMUX_FUNC_CLK_SEL` reader - set this field to select clock-source. 0: do not select anyone clock, 1: 80MHz, 2: FOSC, 3(default): XTAL."]
pub type IOMUX_FUNC_CLK_SEL_R = crate::FieldReader;
#[doc = "Field `IOMUX_FUNC_CLK_SEL` writer - set this field to select clock-source. 0: do not select anyone clock, 1: 80MHz, 2: FOSC, 3(default): XTAL."]
pub type IOMUX_FUNC_CLK_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `IOMUX_FUNC_CLK_EN` reader - Set 1 to enable iomux function clock"]
pub type IOMUX_FUNC_CLK_EN_R = crate::BitReader;
#[doc = "Field `IOMUX_FUNC_CLK_EN` writer - Set 1 to enable iomux function clock"]
pub type IOMUX_FUNC_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 20:21 - set this field to select clock-source. 0: do not select anyone clock, 1: 80MHz, 2: FOSC, 3(default): XTAL."]
    #[inline(always)]
    pub fn iomux_func_clk_sel(&self) -> IOMUX_FUNC_CLK_SEL_R {
        IOMUX_FUNC_CLK_SEL_R::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bit 22 - Set 1 to enable iomux function clock"]
    #[inline(always)]
    pub fn iomux_func_clk_en(&self) -> IOMUX_FUNC_CLK_EN_R {
        IOMUX_FUNC_CLK_EN_R::new(((self.bits >> 22) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IOMUX_CLK_CONF")
            .field("iomux_func_clk_sel", &self.iomux_func_clk_sel())
            .field("iomux_func_clk_en", &self.iomux_func_clk_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 20:21 - set this field to select clock-source. 0: do not select anyone clock, 1: 80MHz, 2: FOSC, 3(default): XTAL."]
    #[inline(always)]
    pub fn iomux_func_clk_sel(&mut self) -> IOMUX_FUNC_CLK_SEL_W<'_, IOMUX_CLK_CONF_SPEC> {
        IOMUX_FUNC_CLK_SEL_W::new(self, 20)
    }
    #[doc = "Bit 22 - Set 1 to enable iomux function clock"]
    #[inline(always)]
    pub fn iomux_func_clk_en(&mut self) -> IOMUX_FUNC_CLK_EN_W<'_, IOMUX_CLK_CONF_SPEC> {
        IOMUX_FUNC_CLK_EN_W::new(self, 22)
    }
}
#[doc = "IOMUX_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`iomux_clk_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`iomux_clk_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IOMUX_CLK_CONF_SPEC;
impl crate::RegisterSpec for IOMUX_CLK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`iomux_clk_conf::R`](R) reader structure"]
impl crate::Readable for IOMUX_CLK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`iomux_clk_conf::W`](W) writer structure"]
impl crate::Writable for IOMUX_CLK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IOMUX_CLK_CONF to value 0x0070_0000"]
impl crate::Resettable for IOMUX_CLK_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0070_0000;
}
