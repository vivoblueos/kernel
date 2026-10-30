#[doc = "Register `CORE_CLK_SEL` reader"]
pub type R = crate::R<CORE_CLK_SEL_SPEC>;
#[doc = "Register `CORE_CLK_SEL` writer"]
pub type W = crate::W<CORE_CLK_SEL_SPEC>;
#[doc = "Field `SPI01_CLK_SEL` reader - When the digital system clock selects PLL clock and the frequency of PLL clock is 480MHz, the value of reg_spi01_clk_sel: 0: SPI0/1 module clock (clk) is 80MHz. 1: SPI0/1 module clock (clk) is 120MHz. 2: SPI0/1 module clock (clk) 160MHz. 3: Not used. When the digital system clock selects PLL clock and the frequency of PLL clock is 320MHz, the value of reg_spi01_clk_sel: 0: SPI0/1 module clock (clk) is 80MHz. 1: SPI0/1 module clock (clk) is 80MHz. 2: SPI0/1 module clock (clk) 160MHz. 3: Not used."]
pub type SPI01_CLK_SEL_R = crate::FieldReader;
#[doc = "Field `SPI01_CLK_SEL` writer - When the digital system clock selects PLL clock and the frequency of PLL clock is 480MHz, the value of reg_spi01_clk_sel: 0: SPI0/1 module clock (clk) is 80MHz. 1: SPI0/1 module clock (clk) is 120MHz. 2: SPI0/1 module clock (clk) 160MHz. 3: Not used. When the digital system clock selects PLL clock and the frequency of PLL clock is 320MHz, the value of reg_spi01_clk_sel: 0: SPI0/1 module clock (clk) is 80MHz. 1: SPI0/1 module clock (clk) is 80MHz. 2: SPI0/1 module clock (clk) 160MHz. 3: Not used."]
pub type SPI01_CLK_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - When the digital system clock selects PLL clock and the frequency of PLL clock is 480MHz, the value of reg_spi01_clk_sel: 0: SPI0/1 module clock (clk) is 80MHz. 1: SPI0/1 module clock (clk) is 120MHz. 2: SPI0/1 module clock (clk) 160MHz. 3: Not used. When the digital system clock selects PLL clock and the frequency of PLL clock is 320MHz, the value of reg_spi01_clk_sel: 0: SPI0/1 module clock (clk) is 80MHz. 1: SPI0/1 module clock (clk) is 80MHz. 2: SPI0/1 module clock (clk) 160MHz. 3: Not used."]
    #[inline(always)]
    pub fn spi01_clk_sel(&self) -> SPI01_CLK_SEL_R {
        SPI01_CLK_SEL_R::new((self.bits & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE_CLK_SEL")
            .field("spi01_clk_sel", &self.spi01_clk_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - When the digital system clock selects PLL clock and the frequency of PLL clock is 480MHz, the value of reg_spi01_clk_sel: 0: SPI0/1 module clock (clk) is 80MHz. 1: SPI0/1 module clock (clk) is 120MHz. 2: SPI0/1 module clock (clk) 160MHz. 3: Not used. When the digital system clock selects PLL clock and the frequency of PLL clock is 320MHz, the value of reg_spi01_clk_sel: 0: SPI0/1 module clock (clk) is 80MHz. 1: SPI0/1 module clock (clk) is 80MHz. 2: SPI0/1 module clock (clk) 160MHz. 3: Not used."]
    #[inline(always)]
    pub fn spi01_clk_sel(&mut self) -> SPI01_CLK_SEL_W<'_, CORE_CLK_SEL_SPEC> {
        SPI01_CLK_SEL_W::new(self, 0)
    }
}
#[doc = "SPI0 module clock select register\n\nYou can [`read`](crate::Reg::read) this register and get [`core_clk_sel::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_clk_sel::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE_CLK_SEL_SPEC;
impl crate::RegisterSpec for CORE_CLK_SEL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core_clk_sel::R`](R) reader structure"]
impl crate::Readable for CORE_CLK_SEL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`core_clk_sel::W`](W) writer structure"]
impl crate::Writable for CORE_CLK_SEL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CORE_CLK_SEL to value 0"]
impl crate::Resettable for CORE_CLK_SEL_SPEC {}
