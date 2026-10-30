#[doc = "Register `CH_ENA_AD0` reader"]
pub type R = crate::R<CH_ENA_AD0_SPEC>;
#[doc = "Register `CH_ENA_AD0` writer"]
pub type W = crate::W<CH_ENA_AD0_SPEC>;
#[doc = "Field `CH_ENA(0-31)` reader - ch%s enable"]
pub type CH_ENA_R = crate::BitReader;
#[doc = "Field `CH_ENA(0-31)` writer - ch%s enable"]
pub type CH_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "ch(0-31) enable"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH_ENA0` field.</div>"]
    #[inline(always)]
    pub fn ch_ena(&self, n: u8) -> CH_ENA_R {
        #[allow(clippy::no_effect)]
        [(); 32][n as usize];
        CH_ENA_R::new(((self.bits >> n) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "ch(0-31) enable"]
    #[inline(always)]
    pub fn ch_ena_iter(&self) -> impl Iterator<Item = CH_ENA_R> + '_ {
        (0..32).map(move |n| CH_ENA_R::new(((self.bits >> n) & 1) != 0))
    }
    #[doc = "Bit 0 - ch0 enable"]
    #[inline(always)]
    pub fn ch_ena0(&self) -> CH_ENA_R {
        CH_ENA_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - ch1 enable"]
    #[inline(always)]
    pub fn ch_ena1(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - ch2 enable"]
    #[inline(always)]
    pub fn ch_ena2(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - ch3 enable"]
    #[inline(always)]
    pub fn ch_ena3(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - ch4 enable"]
    #[inline(always)]
    pub fn ch_ena4(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - ch5 enable"]
    #[inline(always)]
    pub fn ch_ena5(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - ch6 enable"]
    #[inline(always)]
    pub fn ch_ena6(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - ch7 enable"]
    #[inline(always)]
    pub fn ch_ena7(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - ch8 enable"]
    #[inline(always)]
    pub fn ch_ena8(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - ch9 enable"]
    #[inline(always)]
    pub fn ch_ena9(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - ch10 enable"]
    #[inline(always)]
    pub fn ch_ena10(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - ch11 enable"]
    #[inline(always)]
    pub fn ch_ena11(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - ch12 enable"]
    #[inline(always)]
    pub fn ch_ena12(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - ch13 enable"]
    #[inline(always)]
    pub fn ch_ena13(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - ch14 enable"]
    #[inline(always)]
    pub fn ch_ena14(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - ch15 enable"]
    #[inline(always)]
    pub fn ch_ena15(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - ch16 enable"]
    #[inline(always)]
    pub fn ch_ena16(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - ch17 enable"]
    #[inline(always)]
    pub fn ch_ena17(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - ch18 enable"]
    #[inline(always)]
    pub fn ch_ena18(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - ch19 enable"]
    #[inline(always)]
    pub fn ch_ena19(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - ch20 enable"]
    #[inline(always)]
    pub fn ch_ena20(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - ch21 enable"]
    #[inline(always)]
    pub fn ch_ena21(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - ch22 enable"]
    #[inline(always)]
    pub fn ch_ena22(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - ch23 enable"]
    #[inline(always)]
    pub fn ch_ena23(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - ch24 enable"]
    #[inline(always)]
    pub fn ch_ena24(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - ch25 enable"]
    #[inline(always)]
    pub fn ch_ena25(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - ch26 enable"]
    #[inline(always)]
    pub fn ch_ena26(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - ch27 enable"]
    #[inline(always)]
    pub fn ch_ena27(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - ch28 enable"]
    #[inline(always)]
    pub fn ch_ena28(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - ch29 enable"]
    #[inline(always)]
    pub fn ch_ena29(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - ch30 enable"]
    #[inline(always)]
    pub fn ch_ena30(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - ch31 enable"]
    #[inline(always)]
    pub fn ch_ena31(&self) -> CH_ENA_R {
        CH_ENA_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CH_ENA_AD0")
            .field("ch_ena0", &self.ch_ena0())
            .field("ch_ena1", &self.ch_ena1())
            .field("ch_ena2", &self.ch_ena2())
            .field("ch_ena3", &self.ch_ena3())
            .field("ch_ena4", &self.ch_ena4())
            .field("ch_ena5", &self.ch_ena5())
            .field("ch_ena6", &self.ch_ena6())
            .field("ch_ena7", &self.ch_ena7())
            .field("ch_ena8", &self.ch_ena8())
            .field("ch_ena9", &self.ch_ena9())
            .field("ch_ena10", &self.ch_ena10())
            .field("ch_ena11", &self.ch_ena11())
            .field("ch_ena12", &self.ch_ena12())
            .field("ch_ena13", &self.ch_ena13())
            .field("ch_ena14", &self.ch_ena14())
            .field("ch_ena15", &self.ch_ena15())
            .field("ch_ena16", &self.ch_ena16())
            .field("ch_ena17", &self.ch_ena17())
            .field("ch_ena18", &self.ch_ena18())
            .field("ch_ena19", &self.ch_ena19())
            .field("ch_ena20", &self.ch_ena20())
            .field("ch_ena21", &self.ch_ena21())
            .field("ch_ena22", &self.ch_ena22())
            .field("ch_ena23", &self.ch_ena23())
            .field("ch_ena24", &self.ch_ena24())
            .field("ch_ena25", &self.ch_ena25())
            .field("ch_ena26", &self.ch_ena26())
            .field("ch_ena27", &self.ch_ena27())
            .field("ch_ena28", &self.ch_ena28())
            .field("ch_ena29", &self.ch_ena29())
            .field("ch_ena30", &self.ch_ena30())
            .field("ch_ena31", &self.ch_ena31())
            .finish()
    }
}
impl W {
    #[doc = "ch(0-31) enable"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CH_ENA0` field.</div>"]
    #[inline(always)]
    pub fn ch_ena(&mut self, n: u8) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 32][n as usize];
        CH_ENA_W::new(self, n)
    }
    #[doc = "Bit 0 - ch0 enable"]
    #[inline(always)]
    pub fn ch_ena0(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 0)
    }
    #[doc = "Bit 1 - ch1 enable"]
    #[inline(always)]
    pub fn ch_ena1(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 1)
    }
    #[doc = "Bit 2 - ch2 enable"]
    #[inline(always)]
    pub fn ch_ena2(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 2)
    }
    #[doc = "Bit 3 - ch3 enable"]
    #[inline(always)]
    pub fn ch_ena3(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 3)
    }
    #[doc = "Bit 4 - ch4 enable"]
    #[inline(always)]
    pub fn ch_ena4(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 4)
    }
    #[doc = "Bit 5 - ch5 enable"]
    #[inline(always)]
    pub fn ch_ena5(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 5)
    }
    #[doc = "Bit 6 - ch6 enable"]
    #[inline(always)]
    pub fn ch_ena6(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 6)
    }
    #[doc = "Bit 7 - ch7 enable"]
    #[inline(always)]
    pub fn ch_ena7(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 7)
    }
    #[doc = "Bit 8 - ch8 enable"]
    #[inline(always)]
    pub fn ch_ena8(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 8)
    }
    #[doc = "Bit 9 - ch9 enable"]
    #[inline(always)]
    pub fn ch_ena9(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 9)
    }
    #[doc = "Bit 10 - ch10 enable"]
    #[inline(always)]
    pub fn ch_ena10(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 10)
    }
    #[doc = "Bit 11 - ch11 enable"]
    #[inline(always)]
    pub fn ch_ena11(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 11)
    }
    #[doc = "Bit 12 - ch12 enable"]
    #[inline(always)]
    pub fn ch_ena12(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 12)
    }
    #[doc = "Bit 13 - ch13 enable"]
    #[inline(always)]
    pub fn ch_ena13(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 13)
    }
    #[doc = "Bit 14 - ch14 enable"]
    #[inline(always)]
    pub fn ch_ena14(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 14)
    }
    #[doc = "Bit 15 - ch15 enable"]
    #[inline(always)]
    pub fn ch_ena15(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 15)
    }
    #[doc = "Bit 16 - ch16 enable"]
    #[inline(always)]
    pub fn ch_ena16(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 16)
    }
    #[doc = "Bit 17 - ch17 enable"]
    #[inline(always)]
    pub fn ch_ena17(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 17)
    }
    #[doc = "Bit 18 - ch18 enable"]
    #[inline(always)]
    pub fn ch_ena18(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 18)
    }
    #[doc = "Bit 19 - ch19 enable"]
    #[inline(always)]
    pub fn ch_ena19(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 19)
    }
    #[doc = "Bit 20 - ch20 enable"]
    #[inline(always)]
    pub fn ch_ena20(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 20)
    }
    #[doc = "Bit 21 - ch21 enable"]
    #[inline(always)]
    pub fn ch_ena21(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 21)
    }
    #[doc = "Bit 22 - ch22 enable"]
    #[inline(always)]
    pub fn ch_ena22(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 22)
    }
    #[doc = "Bit 23 - ch23 enable"]
    #[inline(always)]
    pub fn ch_ena23(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 23)
    }
    #[doc = "Bit 24 - ch24 enable"]
    #[inline(always)]
    pub fn ch_ena24(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 24)
    }
    #[doc = "Bit 25 - ch25 enable"]
    #[inline(always)]
    pub fn ch_ena25(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 25)
    }
    #[doc = "Bit 26 - ch26 enable"]
    #[inline(always)]
    pub fn ch_ena26(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 26)
    }
    #[doc = "Bit 27 - ch27 enable"]
    #[inline(always)]
    pub fn ch_ena27(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 27)
    }
    #[doc = "Bit 28 - ch28 enable"]
    #[inline(always)]
    pub fn ch_ena28(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 28)
    }
    #[doc = "Bit 29 - ch29 enable"]
    #[inline(always)]
    pub fn ch_ena29(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 29)
    }
    #[doc = "Bit 30 - ch30 enable"]
    #[inline(always)]
    pub fn ch_ena30(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 30)
    }
    #[doc = "Bit 31 - ch31 enable"]
    #[inline(always)]
    pub fn ch_ena31(&mut self) -> CH_ENA_W<'_, CH_ENA_AD0_SPEC> {
        CH_ENA_W::new(self, 31)
    }
}
#[doc = "channel enable register\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_ena_ad0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_ena_ad0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CH_ENA_AD0_SPEC;
impl crate::RegisterSpec for CH_ENA_AD0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch_ena_ad0::R`](R) reader structure"]
impl crate::Readable for CH_ENA_AD0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ch_ena_ad0::W`](W) writer structure"]
impl crate::Writable for CH_ENA_AD0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CH_ENA_AD0 to value 0"]
impl crate::Resettable for CH_ENA_AD0_SPEC {}
