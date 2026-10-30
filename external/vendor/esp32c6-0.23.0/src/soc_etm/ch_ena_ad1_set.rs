#[doc = "Register `CH_ENA_AD1_SET` writer"]
pub type W = crate::W<CH_ENA_AD1_SET_SPEC>;
#[doc = "Field `CH_SET(32-49)` writer - ch%s set"]
pub type CH_SET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<CH_ENA_AD1_SET_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "ch(32-49) set"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH_SET32` field.</div>"]
    #[inline(always)]
    pub fn ch_set(&mut self, n: u8) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 18][n as usize];
        CH_SET_W::new(self, n)
    }
    #[doc = "Bit 0 - ch32 set"]
    #[inline(always)]
    pub fn ch_set32(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 0)
    }
    #[doc = "Bit 1 - ch33 set"]
    #[inline(always)]
    pub fn ch_set33(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 1)
    }
    #[doc = "Bit 2 - ch34 set"]
    #[inline(always)]
    pub fn ch_set34(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 2)
    }
    #[doc = "Bit 3 - ch35 set"]
    #[inline(always)]
    pub fn ch_set35(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 3)
    }
    #[doc = "Bit 4 - ch36 set"]
    #[inline(always)]
    pub fn ch_set36(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 4)
    }
    #[doc = "Bit 5 - ch37 set"]
    #[inline(always)]
    pub fn ch_set37(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 5)
    }
    #[doc = "Bit 6 - ch38 set"]
    #[inline(always)]
    pub fn ch_set38(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 6)
    }
    #[doc = "Bit 7 - ch39 set"]
    #[inline(always)]
    pub fn ch_set39(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 7)
    }
    #[doc = "Bit 8 - ch40 set"]
    #[inline(always)]
    pub fn ch_set40(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 8)
    }
    #[doc = "Bit 9 - ch41 set"]
    #[inline(always)]
    pub fn ch_set41(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 9)
    }
    #[doc = "Bit 10 - ch42 set"]
    #[inline(always)]
    pub fn ch_set42(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 10)
    }
    #[doc = "Bit 11 - ch43 set"]
    #[inline(always)]
    pub fn ch_set43(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 11)
    }
    #[doc = "Bit 12 - ch44 set"]
    #[inline(always)]
    pub fn ch_set44(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 12)
    }
    #[doc = "Bit 13 - ch45 set"]
    #[inline(always)]
    pub fn ch_set45(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 13)
    }
    #[doc = "Bit 14 - ch46 set"]
    #[inline(always)]
    pub fn ch_set46(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 14)
    }
    #[doc = "Bit 15 - ch47 set"]
    #[inline(always)]
    pub fn ch_set47(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 15)
    }
    #[doc = "Bit 16 - ch48 set"]
    #[inline(always)]
    pub fn ch_set48(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 16)
    }
    #[doc = "Bit 17 - ch49 set"]
    #[inline(always)]
    pub fn ch_set49(&mut self) -> CH_SET_W<'_, CH_ENA_AD1_SET_SPEC> {
        CH_SET_W::new(self, 17)
    }
}
#[doc = "channel enable set register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_ena_ad1_set::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CH_ENA_AD1_SET_SPEC;
impl crate::RegisterSpec for CH_ENA_AD1_SET_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`ch_ena_ad1_set::W`](W) writer structure"]
impl crate::Writable for CH_ENA_AD1_SET_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CH_ENA_AD1_SET to value 0"]
impl crate::Resettable for CH_ENA_AD1_SET_SPEC {}
