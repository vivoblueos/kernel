#[doc = "Register `CH_ENA_AD0_SET` writer"]
pub type W = crate::W<CH_ENA_AD0_SET_SPEC>;
#[doc = "Field `CH_SET(0-31)` writer - ch%s set"]
pub type CH_SET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<CH_ENA_AD0_SET_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "ch(0-31) set"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH_SET0` field.</div>"]
    #[inline(always)]
    pub fn ch_set(&mut self, n: u8) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 32][n as usize];
        CH_SET_W::new(self, n)
    }
    #[doc = "Bit 0 - ch0 set"]
    #[inline(always)]
    pub fn ch_set0(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 0)
    }
    #[doc = "Bit 1 - ch1 set"]
    #[inline(always)]
    pub fn ch_set1(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 1)
    }
    #[doc = "Bit 2 - ch2 set"]
    #[inline(always)]
    pub fn ch_set2(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 2)
    }
    #[doc = "Bit 3 - ch3 set"]
    #[inline(always)]
    pub fn ch_set3(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 3)
    }
    #[doc = "Bit 4 - ch4 set"]
    #[inline(always)]
    pub fn ch_set4(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 4)
    }
    #[doc = "Bit 5 - ch5 set"]
    #[inline(always)]
    pub fn ch_set5(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 5)
    }
    #[doc = "Bit 6 - ch6 set"]
    #[inline(always)]
    pub fn ch_set6(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 6)
    }
    #[doc = "Bit 7 - ch7 set"]
    #[inline(always)]
    pub fn ch_set7(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 7)
    }
    #[doc = "Bit 8 - ch8 set"]
    #[inline(always)]
    pub fn ch_set8(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 8)
    }
    #[doc = "Bit 9 - ch9 set"]
    #[inline(always)]
    pub fn ch_set9(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 9)
    }
    #[doc = "Bit 10 - ch10 set"]
    #[inline(always)]
    pub fn ch_set10(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 10)
    }
    #[doc = "Bit 11 - ch11 set"]
    #[inline(always)]
    pub fn ch_set11(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 11)
    }
    #[doc = "Bit 12 - ch12 set"]
    #[inline(always)]
    pub fn ch_set12(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 12)
    }
    #[doc = "Bit 13 - ch13 set"]
    #[inline(always)]
    pub fn ch_set13(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 13)
    }
    #[doc = "Bit 14 - ch14 set"]
    #[inline(always)]
    pub fn ch_set14(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 14)
    }
    #[doc = "Bit 15 - ch15 set"]
    #[inline(always)]
    pub fn ch_set15(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 15)
    }
    #[doc = "Bit 16 - ch16 set"]
    #[inline(always)]
    pub fn ch_set16(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 16)
    }
    #[doc = "Bit 17 - ch17 set"]
    #[inline(always)]
    pub fn ch_set17(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 17)
    }
    #[doc = "Bit 18 - ch18 set"]
    #[inline(always)]
    pub fn ch_set18(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 18)
    }
    #[doc = "Bit 19 - ch19 set"]
    #[inline(always)]
    pub fn ch_set19(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 19)
    }
    #[doc = "Bit 20 - ch20 set"]
    #[inline(always)]
    pub fn ch_set20(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 20)
    }
    #[doc = "Bit 21 - ch21 set"]
    #[inline(always)]
    pub fn ch_set21(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 21)
    }
    #[doc = "Bit 22 - ch22 set"]
    #[inline(always)]
    pub fn ch_set22(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 22)
    }
    #[doc = "Bit 23 - ch23 set"]
    #[inline(always)]
    pub fn ch_set23(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 23)
    }
    #[doc = "Bit 24 - ch24 set"]
    #[inline(always)]
    pub fn ch_set24(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 24)
    }
    #[doc = "Bit 25 - ch25 set"]
    #[inline(always)]
    pub fn ch_set25(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 25)
    }
    #[doc = "Bit 26 - ch26 set"]
    #[inline(always)]
    pub fn ch_set26(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 26)
    }
    #[doc = "Bit 27 - ch27 set"]
    #[inline(always)]
    pub fn ch_set27(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 27)
    }
    #[doc = "Bit 28 - ch28 set"]
    #[inline(always)]
    pub fn ch_set28(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 28)
    }
    #[doc = "Bit 29 - ch29 set"]
    #[inline(always)]
    pub fn ch_set29(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 29)
    }
    #[doc = "Bit 30 - ch30 set"]
    #[inline(always)]
    pub fn ch_set30(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 30)
    }
    #[doc = "Bit 31 - ch31 set"]
    #[inline(always)]
    pub fn ch_set31(&mut self) -> CH_SET_W<'_, CH_ENA_AD0_SET_SPEC> {
        CH_SET_W::new(self, 31)
    }
}
#[doc = "channel enable set register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_ena_ad0_set::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CH_ENA_AD0_SET_SPEC;
impl crate::RegisterSpec for CH_ENA_AD0_SET_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`ch_ena_ad0_set::W`](W) writer structure"]
impl crate::Writable for CH_ENA_AD0_SET_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CH_ENA_AD0_SET to value 0"]
impl crate::Resettable for CH_ENA_AD0_SET_SPEC {}
