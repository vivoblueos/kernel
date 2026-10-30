#[doc = "Register `INT_CLR` writer"]
pub type W = crate::W<INT_CLR_SPEC>;
#[doc = "Field `TIMER_OVF(0-3)` writer - Set this bit to clear the TIMER%s_OVF interrupt."]
pub type TIMER_OVF_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `DUTY_CHNG_END_CH(0-5)` writer - Set this bit to clear the DUTY_CHNG_END_CH%s interrupt."]
pub type DUTY_CHNG_END_CH_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `OVF_CNT_CH(0-5)` writer - Set this bit to clear the OVF_CNT_CH%s interrupt."]
pub type OVF_CNT_CH_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<INT_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Set this bit to clear the TIMER(0-3)_OVF interrupt."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `TIMER0_OVF` field.</div>"]
    #[inline(always)]
    pub fn timer_ovf(&mut self, n: u8) -> TIMER_OVF_W<'_, INT_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 4][n as usize];
        TIMER_OVF_W::new(self, n)
    }
    #[doc = "Bit 0 - Set this bit to clear the TIMER0_OVF interrupt."]
    #[inline(always)]
    pub fn timer0_ovf(&mut self) -> TIMER_OVF_W<'_, INT_CLR_SPEC> {
        TIMER_OVF_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set this bit to clear the TIMER1_OVF interrupt."]
    #[inline(always)]
    pub fn timer1_ovf(&mut self) -> TIMER_OVF_W<'_, INT_CLR_SPEC> {
        TIMER_OVF_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set this bit to clear the TIMER2_OVF interrupt."]
    #[inline(always)]
    pub fn timer2_ovf(&mut self) -> TIMER_OVF_W<'_, INT_CLR_SPEC> {
        TIMER_OVF_W::new(self, 2)
    }
    #[doc = "Bit 3 - Set this bit to clear the TIMER3_OVF interrupt."]
    #[inline(always)]
    pub fn timer3_ovf(&mut self) -> TIMER_OVF_W<'_, INT_CLR_SPEC> {
        TIMER_OVF_W::new(self, 3)
    }
    #[doc = "Set this bit to clear the DUTY_CHNG_END_CH(0-5) interrupt."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `DUTY_CHNG_END_CH0` field.</div>"]
    #[inline(always)]
    pub fn duty_chng_end_ch(&mut self, n: u8) -> DUTY_CHNG_END_CH_W<'_, INT_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 6][n as usize];
        DUTY_CHNG_END_CH_W::new(self, n + 4)
    }
    #[doc = "Bit 4 - Set this bit to clear the DUTY_CHNG_END_CH0 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch0(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_CLR_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 4)
    }
    #[doc = "Bit 5 - Set this bit to clear the DUTY_CHNG_END_CH1 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch1(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_CLR_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 5)
    }
    #[doc = "Bit 6 - Set this bit to clear the DUTY_CHNG_END_CH2 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch2(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_CLR_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 6)
    }
    #[doc = "Bit 7 - Set this bit to clear the DUTY_CHNG_END_CH3 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch3(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_CLR_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 7)
    }
    #[doc = "Bit 8 - Set this bit to clear the DUTY_CHNG_END_CH4 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch4(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_CLR_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 8)
    }
    #[doc = "Bit 9 - Set this bit to clear the DUTY_CHNG_END_CH5 interrupt."]
    #[inline(always)]
    pub fn duty_chng_end_ch5(&mut self) -> DUTY_CHNG_END_CH_W<'_, INT_CLR_SPEC> {
        DUTY_CHNG_END_CH_W::new(self, 9)
    }
    #[doc = "Set this bit to clear the OVF_CNT_CH(0-5) interrupt."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `OVF_CNT_CH0` field.</div>"]
    #[inline(always)]
    pub fn ovf_cnt_ch(&mut self, n: u8) -> OVF_CNT_CH_W<'_, INT_CLR_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 6][n as usize];
        OVF_CNT_CH_W::new(self, n + 12)
    }
    #[doc = "Bit 12 - Set this bit to clear the OVF_CNT_CH0 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch0(&mut self) -> OVF_CNT_CH_W<'_, INT_CLR_SPEC> {
        OVF_CNT_CH_W::new(self, 12)
    }
    #[doc = "Bit 13 - Set this bit to clear the OVF_CNT_CH1 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch1(&mut self) -> OVF_CNT_CH_W<'_, INT_CLR_SPEC> {
        OVF_CNT_CH_W::new(self, 13)
    }
    #[doc = "Bit 14 - Set this bit to clear the OVF_CNT_CH2 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch2(&mut self) -> OVF_CNT_CH_W<'_, INT_CLR_SPEC> {
        OVF_CNT_CH_W::new(self, 14)
    }
    #[doc = "Bit 15 - Set this bit to clear the OVF_CNT_CH3 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch3(&mut self) -> OVF_CNT_CH_W<'_, INT_CLR_SPEC> {
        OVF_CNT_CH_W::new(self, 15)
    }
    #[doc = "Bit 16 - Set this bit to clear the OVF_CNT_CH4 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch4(&mut self) -> OVF_CNT_CH_W<'_, INT_CLR_SPEC> {
        OVF_CNT_CH_W::new(self, 16)
    }
    #[doc = "Bit 17 - Set this bit to clear the OVF_CNT_CH5 interrupt."]
    #[inline(always)]
    pub fn ovf_cnt_ch5(&mut self) -> OVF_CNT_CH_W<'_, INT_CLR_SPEC> {
        OVF_CNT_CH_W::new(self, 17)
    }
}
#[doc = "Interrupt clear bits\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_CLR_SPEC;
impl crate::RegisterSpec for INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`int_clr::W`](W) writer structure"]
impl crate::Writable for INT_CLR_SPEC {
    type Safety = crate::Unsafe;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0x0003_f3ff;
}
#[doc = "`reset()` method sets INT_CLR to value 0"]
impl crate::Resettable for INT_CLR_SPEC {}
