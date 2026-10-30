#[doc = "Register `CH_ENA_AD0_CLR` writer"]
pub type W = crate::W<CH_ENA_AD0_CLR_SPEC>;
#[doc = "Field `CH_CLR(0-31)` writer - ch%s clear"]
pub type CH_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<CH_ENA_AD0_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "ch(0-31) clear"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH_CLR0` field.</div>"]
    #[inline(always)]
    pub fn ch_clr(&mut self, n: u8) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 32][n as usize];
        CH_CLR_W::new(self, n)
    }
    #[doc = "Bit 0 - ch0 clear"]
    #[inline(always)]
    pub fn ch_clr0(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 0)
    }
    #[doc = "Bit 1 - ch1 clear"]
    #[inline(always)]
    pub fn ch_clr1(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 1)
    }
    #[doc = "Bit 2 - ch2 clear"]
    #[inline(always)]
    pub fn ch_clr2(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 2)
    }
    #[doc = "Bit 3 - ch3 clear"]
    #[inline(always)]
    pub fn ch_clr3(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 3)
    }
    #[doc = "Bit 4 - ch4 clear"]
    #[inline(always)]
    pub fn ch_clr4(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 4)
    }
    #[doc = "Bit 5 - ch5 clear"]
    #[inline(always)]
    pub fn ch_clr5(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 5)
    }
    #[doc = "Bit 6 - ch6 clear"]
    #[inline(always)]
    pub fn ch_clr6(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 6)
    }
    #[doc = "Bit 7 - ch7 clear"]
    #[inline(always)]
    pub fn ch_clr7(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 7)
    }
    #[doc = "Bit 8 - ch8 clear"]
    #[inline(always)]
    pub fn ch_clr8(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 8)
    }
    #[doc = "Bit 9 - ch9 clear"]
    #[inline(always)]
    pub fn ch_clr9(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 9)
    }
    #[doc = "Bit 10 - ch10 clear"]
    #[inline(always)]
    pub fn ch_clr10(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 10)
    }
    #[doc = "Bit 11 - ch11 clear"]
    #[inline(always)]
    pub fn ch_clr11(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 11)
    }
    #[doc = "Bit 12 - ch12 clear"]
    #[inline(always)]
    pub fn ch_clr12(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 12)
    }
    #[doc = "Bit 13 - ch13 clear"]
    #[inline(always)]
    pub fn ch_clr13(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 13)
    }
    #[doc = "Bit 14 - ch14 clear"]
    #[inline(always)]
    pub fn ch_clr14(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 14)
    }
    #[doc = "Bit 15 - ch15 clear"]
    #[inline(always)]
    pub fn ch_clr15(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 15)
    }
    #[doc = "Bit 16 - ch16 clear"]
    #[inline(always)]
    pub fn ch_clr16(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 16)
    }
    #[doc = "Bit 17 - ch17 clear"]
    #[inline(always)]
    pub fn ch_clr17(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 17)
    }
    #[doc = "Bit 18 - ch18 clear"]
    #[inline(always)]
    pub fn ch_clr18(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 18)
    }
    #[doc = "Bit 19 - ch19 clear"]
    #[inline(always)]
    pub fn ch_clr19(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 19)
    }
    #[doc = "Bit 20 - ch20 clear"]
    #[inline(always)]
    pub fn ch_clr20(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 20)
    }
    #[doc = "Bit 21 - ch21 clear"]
    #[inline(always)]
    pub fn ch_clr21(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 21)
    }
    #[doc = "Bit 22 - ch22 clear"]
    #[inline(always)]
    pub fn ch_clr22(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 22)
    }
    #[doc = "Bit 23 - ch23 clear"]
    #[inline(always)]
    pub fn ch_clr23(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 23)
    }
    #[doc = "Bit 24 - ch24 clear"]
    #[inline(always)]
    pub fn ch_clr24(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 24)
    }
    #[doc = "Bit 25 - ch25 clear"]
    #[inline(always)]
    pub fn ch_clr25(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 25)
    }
    #[doc = "Bit 26 - ch26 clear"]
    #[inline(always)]
    pub fn ch_clr26(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 26)
    }
    #[doc = "Bit 27 - ch27 clear"]
    #[inline(always)]
    pub fn ch_clr27(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 27)
    }
    #[doc = "Bit 28 - ch28 clear"]
    #[inline(always)]
    pub fn ch_clr28(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 28)
    }
    #[doc = "Bit 29 - ch29 clear"]
    #[inline(always)]
    pub fn ch_clr29(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 29)
    }
    #[doc = "Bit 30 - ch30 clear"]
    #[inline(always)]
    pub fn ch_clr30(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 30)
    }
    #[doc = "Bit 31 - ch31 clear"]
    #[inline(always)]
    pub fn ch_clr31(&mut self) -> CH_CLR_W<'_, CH_ENA_AD0_CLR_SPEC> {
        CH_CLR_W::new(self, 31)
    }
}
#[doc = "channel enable clear register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_ena_ad0_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CH_ENA_AD0_CLR_SPEC;
impl crate::RegisterSpec for CH_ENA_AD0_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`ch_ena_ad0_clr::W`](W) writer structure"]
impl crate::Writable for CH_ENA_AD0_CLR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CH_ENA_AD0_CLR to value 0"]
impl crate::Resettable for CH_ENA_AD0_CLR_SPEC {}
