#[doc = "Register `XTAL32K_CLK_FACTOR` reader"]
pub type R = crate::R<XTAL32K_CLK_FACTOR_SPEC>;
#[doc = "Register `XTAL32K_CLK_FACTOR` writer"]
pub type W = crate::W<XTAL32K_CLK_FACTOR_SPEC>;
#[doc = "Field `XTAL32K_CLK_FACTOR` reader - xtal 32k watch dog backup clock factor"]
pub type XTAL32K_CLK_FACTOR_R = crate::FieldReader<u32>;
#[doc = "Field `XTAL32K_CLK_FACTOR` writer - xtal 32k watch dog backup clock factor"]
pub type XTAL32K_CLK_FACTOR_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - xtal 32k watch dog backup clock factor"]
    #[inline(always)]
    pub fn xtal32k_clk_factor(&self) -> XTAL32K_CLK_FACTOR_R {
        XTAL32K_CLK_FACTOR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("XTAL32K_CLK_FACTOR")
            .field("xtal32k_clk_factor", &self.xtal32k_clk_factor())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - xtal 32k watch dog backup clock factor"]
    #[inline(always)]
    pub fn xtal32k_clk_factor(&mut self) -> XTAL32K_CLK_FACTOR_W<'_, XTAL32K_CLK_FACTOR_SPEC> {
        XTAL32K_CLK_FACTOR_W::new(self, 0)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`xtal32k_clk_factor::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`xtal32k_clk_factor::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct XTAL32K_CLK_FACTOR_SPEC;
impl crate::RegisterSpec for XTAL32K_CLK_FACTOR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`xtal32k_clk_factor::R`](R) reader structure"]
impl crate::Readable for XTAL32K_CLK_FACTOR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`xtal32k_clk_factor::W`](W) writer structure"]
impl crate::Writable for XTAL32K_CLK_FACTOR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets XTAL32K_CLK_FACTOR to value 0"]
impl crate::Resettable for XTAL32K_CLK_FACTOR_SPEC {}
