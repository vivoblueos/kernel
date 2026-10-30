#[doc = "Register `CH_ENA_AD1_CLR` writer"]
pub type W = crate::W<CH_ENA_AD1_CLR_SPEC>;
#[doc = "Field `CH_CLR(32-49)` writer - ch%s clear"]
pub type CH_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<CH_ENA_AD1_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "ch(32-49) clear"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH_CLR32` field.</div>"]
    #[inline(always)]
    pub fn ch_clr(&mut self, n: u8) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 18][n as usize];
        CH_CLR_W::new(self, n)
    }
    #[doc = "Bit 0 - ch32 clear"]
    #[inline(always)]
    pub fn ch_clr32(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 0)
    }
    #[doc = "Bit 1 - ch33 clear"]
    #[inline(always)]
    pub fn ch_clr33(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 1)
    }
    #[doc = "Bit 2 - ch34 clear"]
    #[inline(always)]
    pub fn ch_clr34(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 2)
    }
    #[doc = "Bit 3 - ch35 clear"]
    #[inline(always)]
    pub fn ch_clr35(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 3)
    }
    #[doc = "Bit 4 - ch36 clear"]
    #[inline(always)]
    pub fn ch_clr36(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 4)
    }
    #[doc = "Bit 5 - ch37 clear"]
    #[inline(always)]
    pub fn ch_clr37(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 5)
    }
    #[doc = "Bit 6 - ch38 clear"]
    #[inline(always)]
    pub fn ch_clr38(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 6)
    }
    #[doc = "Bit 7 - ch39 clear"]
    #[inline(always)]
    pub fn ch_clr39(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 7)
    }
    #[doc = "Bit 8 - ch40 clear"]
    #[inline(always)]
    pub fn ch_clr40(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 8)
    }
    #[doc = "Bit 9 - ch41 clear"]
    #[inline(always)]
    pub fn ch_clr41(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 9)
    }
    #[doc = "Bit 10 - ch42 clear"]
    #[inline(always)]
    pub fn ch_clr42(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 10)
    }
    #[doc = "Bit 11 - ch43 clear"]
    #[inline(always)]
    pub fn ch_clr43(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 11)
    }
    #[doc = "Bit 12 - ch44 clear"]
    #[inline(always)]
    pub fn ch_clr44(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 12)
    }
    #[doc = "Bit 13 - ch45 clear"]
    #[inline(always)]
    pub fn ch_clr45(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 13)
    }
    #[doc = "Bit 14 - ch46 clear"]
    #[inline(always)]
    pub fn ch_clr46(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 14)
    }
    #[doc = "Bit 15 - ch47 clear"]
    #[inline(always)]
    pub fn ch_clr47(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 15)
    }
    #[doc = "Bit 16 - ch48 clear"]
    #[inline(always)]
    pub fn ch_clr48(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 16)
    }
    #[doc = "Bit 17 - ch49 clear"]
    #[inline(always)]
    pub fn ch_clr49(&mut self) -> CH_CLR_W<'_, CH_ENA_AD1_CLR_SPEC> {
        CH_CLR_W::new(self, 17)
    }
}
#[doc = "channel enable clear register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_ena_ad1_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CH_ENA_AD1_CLR_SPEC;
impl crate::RegisterSpec for CH_ENA_AD1_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`ch_ena_ad1_clr::W`](W) writer structure"]
impl crate::Writable for CH_ENA_AD1_CLR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CH_ENA_AD1_CLR to value 0"]
impl crate::Resettable for CH_ENA_AD1_CLR_SPEC {}
