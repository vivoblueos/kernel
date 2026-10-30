#[doc = "Register `INT_RAW` reader"]
pub type R = crate::R<INT_RAW_SPEC>;
#[doc = "Register `INT_RAW` writer"]
pub type W = crate::W<INT_RAW_SPEC>;
#[doc = "Field `TIMER_OVF(0-3)` reader - reg_lstimer%s_ovf_int_raw."]
pub type TIMER_OVF_R = crate::BitReader;
#[doc = "Field `TIMER_OVF(0-3)` writer - reg_lstimer%s_ovf_int_raw."]
pub type TIMER_OVF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DUTY_CHNG_END_CH(0-5)` reader - Interrupt raw bit for channel %s. Triggered when the gradual change of duty has finished."]
pub type DUTY_CHNG_END_CH_R = crate::BitReader;
#[doc = "Field `DUTY_CHNG_END_CH(0-5)` writer - Interrupt raw bit for channel %s. Triggered when the gradual change of duty has finished."]
pub type DUTY_CHNG_END_CH_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OVF_CNT_CH(0-5)` reader - Interrupt raw bit for channel %s. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
pub type OVF_CNT_CH_R = crate::BitReader;
#[doc = "Field `OVF_CNT_CH(0-5)` writer - Interrupt raw bit for channel %s. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
pub type OVF_CNT_CH_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "reg_lstimer(0-3)_ovf_int_raw."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `TIMER0_OVF` field.</div>"]
    #[inline(always)]
    pub fn timer_ovf(&self, n: u8) -> TIMER_OVF_R {
        #[allow(clippy::no_effect)]
        [(); 4][n as usize];
        TIMER_OVF_R::new(((self.bits >> n) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "reg_lstimer(0-3)_ovf_int_raw."]
    #[inline(always)]
    pub fn timer_ovf_iter(&self) -> impl Iterator<Item = TIMER_OVF_R> + '_ {
        (0..4).map(move |n| TIMER_OVF_R::new(((self.bits >> n) & 1) != 0))
    }
    #[doc = "Bit 0 - reg_lstimer0_ovf_int_raw."]
    #[inline(always)]
    pub fn timer0_ovf(&self) -> TIMER_OVF_R {
        TIMER_OVF_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - reg_lstimer1_ovf_int_raw."]
    #[inline(always)]
    pub fn timer1_ovf(&self) -> TIMER_OVF_R {
        TIMER_OVF_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - reg_lstimer2_ovf_int_raw."]
    #[inline(always)]
    pub fn timer2_ovf(&self) -> TIMER_OVF_R {
        TIMER_OVF_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - reg_lstimer3_ovf_int_raw."]
    #[inline(always)]
    pub fn timer3_ovf(&self) -> TIMER_OVF_R {
        TIMER_OVF_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Interrupt raw bit for channel (0-5). Triggered when the gradual change of duty has finished."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `DUTY_CHNG_END_CH0` field.</div>"]
    #[inline(always)]
    pub fn duty_chng_end_ch(&self, n: u8) -> DUTY_CHNG_END_CH_R {
        #[allow(clippy::no_effect)]
        [(); 6][n as usize];
        DUTY_CHNG_END_CH_R::new(((self.bits >> (n + 4)) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "Interrupt raw bit for channel (0-5). Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch_iter(&self) -> impl Iterator<Item = DUTY_CHNG_END_CH_R> + '_ {
        (0..6).map(move |n| DUTY_CHNG_END_CH_R::new(((self.bits >> (n + 4)) & 1) != 0))
    }
    #[doc = "Bit 4 - Interrupt raw bit for channel 0. Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch0(&self) -> DUTY_CHNG_END_CH_R {
        DUTY_CHNG_END_CH_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Interrupt raw bit for channel 1. Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch1(&self) -> DUTY_CHNG_END_CH_R {
        DUTY_CHNG_END_CH_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Interrupt raw bit for channel 2. Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch2(&self) -> DUTY_CHNG_END_CH_R {
        DUTY_CHNG_END_CH_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Interrupt raw bit for channel 3. Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch3(&self) -> DUTY_CHNG_END_CH_R {
        DUTY_CHNG_END_CH_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Interrupt raw bit for channel 4. Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch4(&self) -> DUTY_CHNG_END_CH_R {
        DUTY_CHNG_END_CH_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Interrupt raw bit for channel 5. Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch5(&self) -> DUTY_CHNG_END_CH_R {
        DUTY_CHNG_END_CH_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Interrupt raw bit for channel (0-5). Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `OVF_CNT_CH0` field.</div>"]
    #[inline(always)]
    pub fn ovf_cnt_ch(&self, n: u8) -> OVF_CNT_CH_R {
        #[allow(clippy::no_effect)]
        [(); 6][n as usize];
        OVF_CNT_CH_R::new(((self.bits >> (n + 10)) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "Interrupt raw bit for channel (0-5). Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch_iter(&self) -> impl Iterator<Item = OVF_CNT_CH_R> + '_ {
        (0..6).map(move |n| OVF_CNT_CH_R::new(((self.bits >> (n + 10)) & 1) != 0))
    }
    #[doc = "Bit 10 - Interrupt raw bit for channel 0. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch0(&self) -> OVF_CNT_CH_R {
        OVF_CNT_CH_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Interrupt raw bit for channel 1. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch1(&self) -> OVF_CNT_CH_R {
        OVF_CNT_CH_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Interrupt raw bit for channel 2. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch2(&self) -> OVF_CNT_CH_R {
        OVF_CNT_CH_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Interrupt raw bit for channel 3. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch3(&self) -> OVF_CNT_CH_R {
        OVF_CNT_CH_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Interrupt raw bit for channel 4. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch4(&self) -> OVF_CNT_CH_R {
        OVF_CNT_CH_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Interrupt raw bit for channel 5. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch5(&self) -> OVF_CNT_CH_R {
        OVF_CNT_CH_R::new(((self.bits >> 15) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_RAW")
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
    #[doc = "reg_lstimer(0-3)_ovf_int_raw."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `TIMER0_OVF` field.</div>"]
    #[inline(always)]
    pub fn timer_ovf(&mut self, n: u8) -> TIMER_OVF_W<'_, INT_RAW_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 4][n as usize];
        TIMER_OVF_W::new(self, n)
    }
    #[doc = "Bit 0 - reg_lstimer0_ovf_int_raw."]
    #[inline(always)]
    pub fn timer0_ovf(&mut self) -> TIMER_OVF_W<'_, INT_RAW_SPEC> {
        TIMER_OVF_W::new(self, 0)
    }
    #[doc = "Bit 1 - reg_lstimer1_ovf_int_raw."]
    #[inline(always)]
    pub fn timer1_ovf(&mut self) -> TIMER_OVF_W<'_, INT_RAW_SPEC> {
        TIMER_OVF_W::new(self, 1)
    }
    #[doc = "Bit 2 - reg_lstimer2_ovf_int_raw."]
    #[inline(always)]
    pub fn timer2_ovf(&mut self) -> TIMER_OVF_W<'_, INT_RAW_SPEC> {
        TIMER_OVF_W::new(self, 2)
    }
    #[doc = "Bit 3 - reg_lstimer3_ovf_int_raw."]
    #[inline(always)]
    pub fn timer3_ovf(&mut self) -> TIMER_OVF_W<'_, INT_RAW_SPEC> {
        TIMER_OVF_W::new(self, 3)
    }
    #[doc = "Interrupt raw bit for channel (0-5). Triggered when the gradual change of duty has finished."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `DUTY_CHNG_END_CH0` field.</div>"]
    #[inline(always)]
    pub fn duty_chng_end_ch(&mut self, n: u8) -> DUTY_CHNG_END_CH_W<'_, INT_RAW_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 6][n as usize];
        DUTY_CHNG_END_CH_W::new(self, n + 4)
    }
    #[doc = "Bit 4 - Interrupt raw bit for channel 0. Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch0(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_RAW_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 4)
    }
    #[doc = "Bit 5 - Interrupt raw bit for channel 1. Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch1(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_RAW_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 5)
    }
    #[doc = "Bit 6 - Interrupt raw bit for channel 2. Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch2(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_RAW_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 6)
    }
    #[doc = "Bit 7 - Interrupt raw bit for channel 3. Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch3(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_RAW_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 7)
    }
    #[doc = "Bit 8 - Interrupt raw bit for channel 4. Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch4(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_RAW_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 8)
    }
    #[doc = "Bit 9 - Interrupt raw bit for channel 5. Triggered when the gradual change of duty has finished."]
    #[inline(always)]
    pub fn duty_chng_end_ch5(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_RAW_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 9)
    }
    #[doc = "Interrupt raw bit for channel (0-5). Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `OVF_CNT_CH0` field.</div>"]
    #[inline(always)]
    pub fn ovf_cnt_ch(&mut self, n: u8) -> OVF_CNT_CH_W<'_, INT_RAW_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 6][n as usize];
        OVF_CNT_CH_W::new(self, n + 10)
    }
    #[doc = "Bit 10 - Interrupt raw bit for channel 0. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch0(&mut self) -> OVF_CNT_CH_W<'_, INT_RAW_SPEC> {
        OVF_CNT_CH_W::new(self, 10)
    }
    #[doc = "Bit 11 - Interrupt raw bit for channel 1. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch1(&mut self) -> OVF_CNT_CH_W<'_, INT_RAW_SPEC> {
        OVF_CNT_CH_W::new(self, 11)
    }
    #[doc = "Bit 12 - Interrupt raw bit for channel 2. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch2(&mut self) -> OVF_CNT_CH_W<'_, INT_RAW_SPEC> {
        OVF_CNT_CH_W::new(self, 12)
    }
    #[doc = "Bit 13 - Interrupt raw bit for channel 3. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch3(&mut self) -> OVF_CNT_CH_W<'_, INT_RAW_SPEC> {
        OVF_CNT_CH_W::new(self, 13)
    }
    #[doc = "Bit 14 - Interrupt raw bit for channel 4. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch4(&mut self) -> OVF_CNT_CH_W<'_, INT_RAW_SPEC> {
        OVF_CNT_CH_W::new(self, 14)
    }
    #[doc = "Bit 15 - Interrupt raw bit for channel 5. Triggered when the OVF_CNT has reached the value specified by LEDC.CHx.CONF0.OVF_NUM."]
    #[inline(always)]
    pub fn ovf_cnt_ch5(&mut self) -> OVF_CNT_CH_W<'_, INT_RAW_SPEC> {
        OVF_CNT_CH_W::new(self, 15)
    }
}
#[doc = "LEDC_INT_RAW.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_raw::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_RAW_SPEC;
impl crate::RegisterSpec for INT_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_raw::R`](R) reader structure"]
impl crate::Readable for INT_RAW_SPEC {}
#[doc = "`write(|w| ..)` method takes [`int_raw::W`](W) writer structure"]
impl crate::Writable for INT_RAW_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_RAW to value 0"]
impl crate::Resettable for INT_RAW_SPEC {}
