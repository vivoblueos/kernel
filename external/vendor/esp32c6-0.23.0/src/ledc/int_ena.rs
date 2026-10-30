#[doc = "Register `INT_ENA` reader"]
pub type R = crate::R<INT_ENA_SPEC>;
#[doc = "Register `INT_ENA` writer"]
pub type W = crate::W<INT_ENA_SPEC>;
#[doc = "Field `TIMER_OVF(0-3)` reader - The interrupt enable bit for the TIMER%s_OVF interrupt."]
pub type TIMER_OVF_R = crate::BitReader;
#[doc = "Field `TIMER_OVF(0-3)` writer - The interrupt enable bit for the TIMER%s_OVF interrupt."]
pub type TIMER_OVF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DUTY_CHNG_END_CH(0-5)` reader - The interrupt enable bit for the DUTY_CHNG_END_CH%s interrupt."]
pub type DUTY_CHNG_END_CH_R = crate::BitReader;
#[doc = "Field `DUTY_CHNG_END_CH(0-5)` writer - The interrupt enable bit for the DUTY_CHNG_END_CH%s interrupt."]
pub type DUTY_CHNG_END_CH_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OVF_CNT_CH(0-5)` reader - The interrupt enable bit for the OVF_CNT_CH%s interrupt."]
pub type OVF_CNT_CH_R = crate::BitReader;
#[doc = "Field `OVF_CNT_CH(0-5)` writer - The interrupt enable bit for the OVF_CNT_CH%s interrupt."]
pub type OVF_CNT_CH_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "The interrupt enable bit for the TIMER(0-3)_OVF interrupt."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `TIMER0_OVF` field.</div>"]
    #[inline(always)]
    pub fn timer_ovf(&self, n: u8) -> TIMER_OVF_R {
        #[allow(clippy::no_effect)]
        [(); 4][n as usize];
        TIMER_OVF_R::new(((self.bits >> n) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "The interrupt enable bit for the TIMER(0-3)_OVF interrupt."]
    #[inline(always)]
    pub fn timer_ovf_iter(&self) -> impl Iterator<Item = TIMER_OVF_R> + '_ {
        (0..4).map(move |n| TIMER_OVF_R::new(((self.bits >> n) & 1) != 0))
    }
    #[doc = "Bit 0 - The interrupt enable bit for the TIMER0_OVF interrupt."]
    #[inline(always)]
    pub fn timer0_ovf(&self) -> TIMER_OVF_R {
        TIMER_OVF_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The interrupt enable bit for the TIMER1_OVF interrupt."]
    #[inline(always)]
    pub fn timer1_ovf(&self) -> TIMER_OVF_R {
        TIMER_OVF_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The interrupt enable bit for the TIMER2_OVF interrupt."]
    #[inline(always)]
    pub fn timer2_ovf(&self) -> TIMER_OVF_R {
        TIMER_OVF_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The interrupt enable bit for the TIMER3_OVF interrupt."]
    #[inline(always)]
    pub fn timer3_ovf(&self) -> TIMER_OVF_R {
        TIMER_OVF_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "The interrupt enable bit for the DUTY_CHNG_END_CH(0-5) interrupt."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `DUTY_CHNG_END_CH0` field.</div>"]
    #[inline(always)]
    pub fn duty_chng_end_ch(&self, n: u8) -> DUTY_CHNG_END_CH_R {
        #[allow(clippy::no_effect)]
        [(); 6][n as usize];
        DUTY_CHNG_END_CH_R::new(((self.bits >> (n + 4)) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "The interrupt enable bit for the DUTY_CHNG_END_CH(0-5) interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch_iter(&self) -> impl Iterator<Item = DUTY_CHNG_END_CH_R> + '_ {
        (0..6).map(move |n| DUTY_CHNG_END_CH_R::new(((self.bits >> (n + 4)) & 1) != 0))
    }
    #[doc = "Bit 4 - The interrupt enable bit for the DUTY_CHNG_END_CH0 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch0(&self) -> DUTY_CHNG_END_CH_R {
        DUTY_CHNG_END_CH_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The interrupt enable bit for the DUTY_CHNG_END_CH1 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch1(&self) -> DUTY_CHNG_END_CH_R {
        DUTY_CHNG_END_CH_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The interrupt enable bit for the DUTY_CHNG_END_CH2 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch2(&self) -> DUTY_CHNG_END_CH_R {
        DUTY_CHNG_END_CH_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The interrupt enable bit for the DUTY_CHNG_END_CH3 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch3(&self) -> DUTY_CHNG_END_CH_R {
        DUTY_CHNG_END_CH_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The interrupt enable bit for the DUTY_CHNG_END_CH4 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch4(&self) -> DUTY_CHNG_END_CH_R {
        DUTY_CHNG_END_CH_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The interrupt enable bit for the DUTY_CHNG_END_CH5 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch5(&self) -> DUTY_CHNG_END_CH_R {
        DUTY_CHNG_END_CH_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "The interrupt enable bit for the OVF_CNT_CH(0-5) interrupt."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `OVF_CNT_CH0` field.</div>"]
    #[inline(always)]
    pub fn ovf_cnt_ch(&self, n: u8) -> OVF_CNT_CH_R {
        #[allow(clippy::no_effect)]
        [(); 6][n as usize];
        OVF_CNT_CH_R::new(((self.bits >> (n + 12)) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "The interrupt enable bit for the OVF_CNT_CH(0-5) interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch_iter(&self) -> impl Iterator<Item = OVF_CNT_CH_R> + '_ {
        (0..6).map(move |n| OVF_CNT_CH_R::new(((self.bits >> (n + 12)) & 1) != 0))
    }
    #[doc = "Bit 12 - The interrupt enable bit for the OVF_CNT_CH0 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch0(&self) -> OVF_CNT_CH_R {
        OVF_CNT_CH_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - The interrupt enable bit for the OVF_CNT_CH1 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch1(&self) -> OVF_CNT_CH_R {
        OVF_CNT_CH_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - The interrupt enable bit for the OVF_CNT_CH2 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch2(&self) -> OVF_CNT_CH_R {
        OVF_CNT_CH_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - The interrupt enable bit for the OVF_CNT_CH3 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch3(&self) -> OVF_CNT_CH_R {
        OVF_CNT_CH_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - The interrupt enable bit for the OVF_CNT_CH4 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch4(&self) -> OVF_CNT_CH_R {
        OVF_CNT_CH_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - The interrupt enable bit for the OVF_CNT_CH5 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch5(&self) -> OVF_CNT_CH_R {
        OVF_CNT_CH_R::new(((self.bits >> 17) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_ENA")
            .field("timer0_ovf", &self.timer0_ovf())
            .field("timer1_ovf", &self.timer1_ovf())
            .field("timer2_ovf", &self.timer2_ovf())
            .field("timer3_ovf", &self.timer3_ovf())
            .field("duty_chng_end_ch0", &self.duty_chng_end_ch0())
            .field("duty_chng_end_ch1", &self.duty_chng_end_ch1())
            .field("duty_chng_end_ch2", &self.duty_chng_end_ch2())
            .field("duty_chng_end_ch3", &self.duty_chng_end_ch3())
            .field("duty_chng_end_ch4", &self.duty_chng_end_ch4())
            .field("duty_chng_end_ch5", &self.duty_chng_end_ch5())
            .field("ovf_cnt_ch0", &self.ovf_cnt_ch0())
            .field("ovf_cnt_ch1", &self.ovf_cnt_ch1())
            .field("ovf_cnt_ch2", &self.ovf_cnt_ch2())
            .field("ovf_cnt_ch3", &self.ovf_cnt_ch3())
            .field("ovf_cnt_ch4", &self.ovf_cnt_ch4())
            .field("ovf_cnt_ch5", &self.ovf_cnt_ch5())
            .finish()
    }
}
impl W {
    #[doc = "The interrupt enable bit for the TIMER(0-3)_OVF interrupt."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `TIMER0_OVF` field.</div>"]
    #[inline(always)]
    pub fn timer_ovf(&mut self, n: u8) -> TIMER_OVF_W<'_, INT_ENA_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 4][n as usize];
        TIMER_OVF_W::new(self, n)
    }
    #[doc = "Bit 0 - The interrupt enable bit for the TIMER0_OVF interrupt."]
    #[inline(always)]
    pub fn timer0_ovf(&mut self) -> TIMER_OVF_W<'_, INT_ENA_SPEC> {
        TIMER_OVF_W::new(self, 0)
    }
    #[doc = "Bit 1 - The interrupt enable bit for the TIMER1_OVF interrupt."]
    #[inline(always)]
    pub fn timer1_ovf(&mut self) -> TIMER_OVF_W<'_, INT_ENA_SPEC> {
        TIMER_OVF_W::new(self, 1)
    }
    #[doc = "Bit 2 - The interrupt enable bit for the TIMER2_OVF interrupt."]
    #[inline(always)]
    pub fn timer2_ovf(&mut self) -> TIMER_OVF_W<'_, INT_ENA_SPEC> {
        TIMER_OVF_W::new(self, 2)
    }
    #[doc = "Bit 3 - The interrupt enable bit for the TIMER3_OVF interrupt."]
    #[inline(always)]
    pub fn timer3_ovf(&mut self) -> TIMER_OVF_W<'_, INT_ENA_SPEC> {
        TIMER_OVF_W::new(self, 3)
    }
    #[doc = "The interrupt enable bit for the DUTY_CHNG_END_CH(0-5) interrupt."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `DUTY_CHNG_END_CH0` field.</div>"]
    #[inline(always)]
    pub fn duty_chng_end_ch(&mut self, n: u8) -> DUTY_CHNG_END_CH_W<'_, INT_ENA_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 6][n as usize];
        DUTY_CHNG_END_CH_W::new(self, n + 4)
    }
    #[doc = "Bit 4 - The interrupt enable bit for the DUTY_CHNG_END_CH0 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch0(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_ENA_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 4)
    }
    #[doc = "Bit 5 - The interrupt enable bit for the DUTY_CHNG_END_CH1 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch1(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_ENA_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 5)
    }
    #[doc = "Bit 6 - The interrupt enable bit for the DUTY_CHNG_END_CH2 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch2(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_ENA_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 6)
    }
    #[doc = "Bit 7 - The interrupt enable bit for the DUTY_CHNG_END_CH3 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch3(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_ENA_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 7)
    }
    #[doc = "Bit 8 - The interrupt enable bit for the DUTY_CHNG_END_CH4 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch4(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_ENA_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 8)
    }
    #[doc = "Bit 9 - The interrupt enable bit for the DUTY_CHNG_END_CH5 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch5(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_ENA_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 9)
    }
    #[doc = "The interrupt enable bit for the OVF_CNT_CH(0-5) interrupt."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `OVF_CNT_CH0` field.</div>"]
    #[inline(always)]
    pub fn ovf_cnt_ch(&mut self, n: u8) -> OVF_CNT_CH_W<'_, INT_ENA_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 6][n as usize];
        OVF_CNT_CH_W::new(self, n + 12)
    }
    #[doc = "Bit 12 - The interrupt enable bit for the OVF_CNT_CH0 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch0(&mut self) -> OVF_CNT_CH_W<'_, INT_ENA_SPEC> {
        OVF_CNT_CH_W::new(self, 12)
    }
    #[doc = "Bit 13 - The interrupt enable bit for the OVF_CNT_CH1 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch1(&mut self) -> OVF_CNT_CH_W<'_, INT_ENA_SPEC> {
        OVF_CNT_CH_W::new(self, 13)
    }
    #[doc = "Bit 14 - The interrupt enable bit for the OVF_CNT_CH2 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch2(&mut self) -> OVF_CNT_CH_W<'_, INT_ENA_SPEC> {
        OVF_CNT_CH_W::new(self, 14)
    }
    #[doc = "Bit 15 - The interrupt enable bit for the OVF_CNT_CH3 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch3(&mut self) -> OVF_CNT_CH_W<'_, INT_ENA_SPEC> {
        OVF_CNT_CH_W::new(self, 15)
    }
    #[doc = "Bit 16 - The interrupt enable bit for the OVF_CNT_CH4 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch4(&mut self) -> OVF_CNT_CH_W<'_, INT_ENA_SPEC> {
        OVF_CNT_CH_W::new(self, 16)
    }
    #[doc = "Bit 17 - The interrupt enable bit for the OVF_CNT_CH5 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch5(&mut self) -> OVF_CNT_CH_W<'_, INT_ENA_SPEC> {
        OVF_CNT_CH_W::new(self, 17)
    }
}
#[doc = "Interrupt enable bits\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_ENA_SPEC;
impl crate::RegisterSpec for INT_ENA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_ena::R`](R) reader structure"]
impl crate::Readable for INT_ENA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`int_ena::W`](W) writer structure"]
impl crate::Writable for INT_ENA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_ENA to value 0"]
impl crate::Resettable for INT_ENA_SPEC {}
