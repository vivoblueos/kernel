#[doc = "Register `LPMEM_FORCE` reader"]
pub type R = crate::R<LPMEM_FORCE_SPEC>;
#[doc = "Register `LPMEM_FORCE` writer"]
pub type W = crate::W<LPMEM_FORCE_SPEC>;
#[doc = "Field `LPMEM_CLK_FORCE_ON` reader - need_des"]
pub type LPMEM_CLK_FORCE_ON_R = crate::BitReader;
#[doc = "Field `LPMEM_CLK_FORCE_ON` writer - need_des"]
pub type LPMEM_CLK_FORCE_ON_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lpmem_clk_force_on(&self) -> LPMEM_CLK_FORCE_ON_R {
        LPMEM_CLK_FORCE_ON_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LPMEM_FORCE")
            .field("lpmem_clk_force_on", &self.lpmem_clk_force_on())
            .finish()
    }
}
impl W {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lpmem_clk_force_on(&mut self) -> LPMEM_CLK_FORCE_ON_W<'_, LPMEM_FORCE_SPEC> {
        LPMEM_CLK_FORCE_ON_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`lpmem_force::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lpmem_force::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LPMEM_FORCE_SPEC;
impl crate::RegisterSpec for LPMEM_FORCE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lpmem_force::R`](R) reader structure"]
impl crate::Readable for LPMEM_FORCE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`lpmem_force::W`](W) writer structure"]
impl crate::Writable for LPMEM_FORCE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LPMEM_FORCE to value 0"]
impl crate::Resettable for LPMEM_FORCE_SPEC {}
