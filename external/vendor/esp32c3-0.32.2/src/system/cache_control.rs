#[doc = "Register `CACHE_CONTROL` reader"]
pub type R = crate::R<CACHE_CONTROL_SPEC>;
#[doc = "Register `CACHE_CONTROL` writer"]
pub type W = crate::W<CACHE_CONTROL_SPEC>;
#[doc = "Field `ICACHE_CLK_ON` reader - reg_icache_clk_on"]
pub type ICACHE_CLK_ON_R = crate::BitReader;
#[doc = "Field `ICACHE_CLK_ON` writer - reg_icache_clk_on"]
pub type ICACHE_CLK_ON_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ICACHE_RESET` reader - reg_icache_reset"]
pub type ICACHE_RESET_R = crate::BitReader;
#[doc = "Field `ICACHE_RESET` writer - reg_icache_reset"]
pub type ICACHE_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DCACHE_CLK_ON` reader - reg_dcache_clk_on"]
pub type DCACHE_CLK_ON_R = crate::BitReader;
#[doc = "Field `DCACHE_CLK_ON` writer - reg_dcache_clk_on"]
pub type DCACHE_CLK_ON_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DCACHE_RESET` reader - reg_dcache_reset"]
pub type DCACHE_RESET_R = crate::BitReader;
#[doc = "Field `DCACHE_RESET` writer - reg_dcache_reset"]
pub type DCACHE_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - reg_icache_clk_on"]
    #[inline(always)]
    pub fn icache_clk_on(&self) -> ICACHE_CLK_ON_R {
        ICACHE_CLK_ON_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - reg_icache_reset"]
    #[inline(always)]
    pub fn icache_reset(&self) -> ICACHE_RESET_R {
        ICACHE_RESET_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - reg_dcache_clk_on"]
    #[inline(always)]
    pub fn dcache_clk_on(&self) -> DCACHE_CLK_ON_R {
        DCACHE_CLK_ON_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - reg_dcache_reset"]
    #[inline(always)]
    pub fn dcache_reset(&self) -> DCACHE_RESET_R {
        DCACHE_RESET_R::new(((self.bits >> 3) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_CONTROL")
            .field("icache_clk_on", &self.icache_clk_on())
            .field("icache_reset", &self.icache_reset())
            .field("dcache_clk_on", &self.dcache_clk_on())
            .field("dcache_reset", &self.dcache_reset())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - reg_icache_clk_on"]
    #[inline(always)]
    pub fn icache_clk_on(&mut self) -> ICACHE_CLK_ON_W<'_, CACHE_CONTROL_SPEC> {
        ICACHE_CLK_ON_W::new(self, 0)
    }
    #[doc = "Bit 1 - reg_icache_reset"]
    #[inline(always)]
    pub fn icache_reset(&mut self) -> ICACHE_RESET_W<'_, CACHE_CONTROL_SPEC> {
        ICACHE_RESET_W::new(self, 1)
    }
    #[doc = "Bit 2 - reg_dcache_clk_on"]
    #[inline(always)]
    pub fn dcache_clk_on(&mut self) -> DCACHE_CLK_ON_W<'_, CACHE_CONTROL_SPEC> {
        DCACHE_CLK_ON_W::new(self, 2)
    }
    #[doc = "Bit 3 - reg_dcache_reset"]
    #[inline(always)]
    pub fn dcache_reset(&mut self) -> DCACHE_RESET_W<'_, CACHE_CONTROL_SPEC> {
        DCACHE_RESET_W::new(self, 3)
    }
}
#[doc = "cache control register\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_control::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_control::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_CONTROL_SPEC;
impl crate::RegisterSpec for CACHE_CONTROL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_control::R`](R) reader structure"]
impl crate::Readable for CACHE_CONTROL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cache_control::W`](W) writer structure"]
impl crate::Writable for CACHE_CONTROL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CACHE_CONTROL to value 0x05"]
impl crate::Resettable for CACHE_CONTROL_SPEC {
    const RESET_VALUE: u32 = 0x05;
}
