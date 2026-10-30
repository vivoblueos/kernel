#[doc = "Register `EDMA_CTRL` reader"]
pub type R = crate::R<EDMA_CTRL_SPEC>;
#[doc = "Register `EDMA_CTRL` writer"]
pub type W = crate::W<EDMA_CTRL_SPEC>;
#[doc = "Field `EDMA_CLK_ON` reader - reg_edma_clk_on"]
pub type EDMA_CLK_ON_R = crate::BitReader;
#[doc = "Field `EDMA_CLK_ON` writer - reg_edma_clk_on"]
pub type EDMA_CLK_ON_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EDMA_RESET` reader - reg_edma_reset"]
pub type EDMA_RESET_R = crate::BitReader;
#[doc = "Field `EDMA_RESET` writer - reg_edma_reset"]
pub type EDMA_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - reg_edma_clk_on"]
    #[inline(always)]
    pub fn edma_clk_on(&self) -> EDMA_CLK_ON_R {
        EDMA_CLK_ON_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - reg_edma_reset"]
    #[inline(always)]
    pub fn edma_reset(&self) -> EDMA_RESET_R {
        EDMA_RESET_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("EDMA_CTRL")
            .field("edma_clk_on", &self.edma_clk_on())
            .field("edma_reset", &self.edma_reset())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - reg_edma_clk_on"]
    #[inline(always)]
    pub fn edma_clk_on(&mut self) -> EDMA_CLK_ON_W<'_, EDMA_CTRL_SPEC> {
        EDMA_CLK_ON_W::new(self, 0)
    }
    #[doc = "Bit 1 - reg_edma_reset"]
    #[inline(always)]
    pub fn edma_reset(&mut self) -> EDMA_RESET_W<'_, EDMA_CTRL_SPEC> {
        EDMA_RESET_W::new(self, 1)
    }
}
#[doc = "EDMA clock and reset register\n\nYou can [`read`](crate::Reg::read) this register and get [`edma_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`edma_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct EDMA_CTRL_SPEC;
impl crate::RegisterSpec for EDMA_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`edma_ctrl::R`](R) reader structure"]
impl crate::Readable for EDMA_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`edma_ctrl::W`](W) writer structure"]
impl crate::Writable for EDMA_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets EDMA_CTRL to value 0x01"]
impl crate::Resettable for EDMA_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
