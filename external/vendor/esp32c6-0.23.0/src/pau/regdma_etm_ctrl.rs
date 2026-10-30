#[doc = "Register `REGDMA_ETM_CTRL` writer"]
pub type W = crate::W<REGDMA_ETM_CTRL_SPEC>;
#[doc = "Field `ETM_START_0` writer - etm_start_0 reg"]
pub type ETM_START_0_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ETM_START_1` writer - etm_start_1 reg"]
pub type ETM_START_1_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ETM_START_2` writer - etm_start_2 reg"]
pub type ETM_START_2_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ETM_START_3` writer - etm_start_3 reg"]
pub type ETM_START_3_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<REGDMA_ETM_CTRL_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - etm_start_0 reg"]
    #[inline(always)]
    pub fn etm_start_0(&mut self) -> ETM_START_0_W<'_, REGDMA_ETM_CTRL_SPEC> {
        ETM_START_0_W::new(self, 0)
    }
    #[doc = "Bit 1 - etm_start_1 reg"]
    #[inline(always)]
    pub fn etm_start_1(&mut self) -> ETM_START_1_W<'_, REGDMA_ETM_CTRL_SPEC> {
        ETM_START_1_W::new(self, 1)
    }
    #[doc = "Bit 2 - etm_start_2 reg"]
    #[inline(always)]
    pub fn etm_start_2(&mut self) -> ETM_START_2_W<'_, REGDMA_ETM_CTRL_SPEC> {
        ETM_START_2_W::new(self, 2)
    }
    #[doc = "Bit 3 - etm_start_3 reg"]
    #[inline(always)]
    pub fn etm_start_3(&mut self) -> ETM_START_3_W<'_, REGDMA_ETM_CTRL_SPEC> {
        ETM_START_3_W::new(self, 3)
    }
}
#[doc = "ETM start ctrl reg\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`regdma_etm_ctrl::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REGDMA_ETM_CTRL_SPEC;
impl crate::RegisterSpec for REGDMA_ETM_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`regdma_etm_ctrl::W`](W) writer structure"]
impl crate::Writable for REGDMA_ETM_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets REGDMA_ETM_CTRL to value 0"]
impl crate::Resettable for REGDMA_ETM_CTRL_SPEC {}
