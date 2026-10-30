#[doc = "Register `POWER_CK_WAIT_CNTL` reader"]
pub type R = crate::R<POWER_CK_WAIT_CNTL_SPEC>;
#[doc = "Register `POWER_CK_WAIT_CNTL` writer"]
pub type W = crate::W<POWER_CK_WAIT_CNTL_SPEC>;
#[doc = "Field `WAIT_XTL_STABLE` reader - need_des"]
pub type WAIT_XTL_STABLE_R = crate::FieldReader<u16>;
#[doc = "Field `WAIT_XTL_STABLE` writer - need_des"]
pub type WAIT_XTL_STABLE_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `WAIT_PLL_STABLE` reader - need_des"]
pub type WAIT_PLL_STABLE_R = crate::FieldReader<u16>;
#[doc = "Field `WAIT_PLL_STABLE` writer - need_des"]
pub type WAIT_PLL_STABLE_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - need_des"]
    #[inline(always)]
    pub fn wait_xtl_stable(&self) -> WAIT_XTL_STABLE_R {
        WAIT_XTL_STABLE_R::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:31 - need_des"]
    #[inline(always)]
    pub fn wait_pll_stable(&self) -> WAIT_PLL_STABLE_R {
        WAIT_PLL_STABLE_R::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("POWER_CK_WAIT_CNTL")
            .field("wait_xtl_stable", &self.wait_xtl_stable())
            .field("wait_pll_stable", &self.wait_pll_stable())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - need_des"]
    #[inline(always)]
    pub fn wait_xtl_stable(&mut self) -> WAIT_XTL_STABLE_W<'_, POWER_CK_WAIT_CNTL_SPEC> {
        WAIT_XTL_STABLE_W::new(self, 0)
    }
    #[doc = "Bits 16:31 - need_des"]
    #[inline(always)]
    pub fn wait_pll_stable(&mut self) -> WAIT_PLL_STABLE_W<'_, POWER_CK_WAIT_CNTL_SPEC> {
        WAIT_PLL_STABLE_W::new(self, 16)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`power_ck_wait_cntl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`power_ck_wait_cntl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct POWER_CK_WAIT_CNTL_SPEC;
impl crate::RegisterSpec for POWER_CK_WAIT_CNTL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`power_ck_wait_cntl::R`](R) reader structure"]
impl crate::Readable for POWER_CK_WAIT_CNTL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`power_ck_wait_cntl::W`](W) writer structure"]
impl crate::Writable for POWER_CK_WAIT_CNTL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets POWER_CK_WAIT_CNTL to value 0x0100_0100"]
impl crate::Resettable for POWER_CK_WAIT_CNTL_SPEC {
    const RESET_VALUE: u32 = 0x0100_0100;
}
