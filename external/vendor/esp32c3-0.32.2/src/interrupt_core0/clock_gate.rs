#[doc = "Register `CLOCK_GATE` reader"]
pub type R = crate::R<CLOCK_GATE_SPEC>;
#[doc = "Register `CLOCK_GATE` writer"]
pub type W = crate::W<CLOCK_GATE_SPEC>;
#[doc = "Field `REG_CLK_EN` reader - reg_core0_reg_clk_en"]
pub type REG_CLK_EN_R = crate::BitReader;
#[doc = "Field `REG_CLK_EN` writer - reg_core0_reg_clk_en"]
pub type REG_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - reg_core0_reg_clk_en"]
    #[inline(always)]
    pub fn reg_clk_en(&self) -> REG_CLK_EN_R {
        REG_CLK_EN_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLOCK_GATE")
            .field("reg_clk_en", &self.reg_clk_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - reg_core0_reg_clk_en"]
    #[inline(always)]
    pub fn reg_clk_en(&mut self) -> REG_CLK_EN_W<'_, CLOCK_GATE_SPEC> {
        REG_CLK_EN_W::new(self, 0)
    }
}
#[doc = "mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`clock_gate::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clock_gate::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLOCK_GATE_SPEC;
impl crate::RegisterSpec for CLOCK_GATE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clock_gate::R`](R) reader structure"]
impl crate::Readable for CLOCK_GATE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clock_gate::W`](W) writer structure"]
impl crate::Writable for CLOCK_GATE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLOCK_GATE to value 0x01"]
impl crate::Resettable for CLOCK_GATE_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
