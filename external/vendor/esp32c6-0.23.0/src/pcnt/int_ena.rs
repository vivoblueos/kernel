#[doc = "Register `INT_ENA` reader"]
pub type R = crate::R<INT_ENA_SPEC>;
#[doc = "Register `INT_ENA` writer"]
pub type W = crate::W<INT_ENA_SPEC>;
#[doc = "Field `CNT_THR_EVENT_U(0-3)` reader - The interrupt enable bit for the PCNT_CNT_THR_EVENT_U%s_INT interrupt."]
pub type CNT_THR_EVENT_U_R = crate::BitReader;
#[doc = "Field `CNT_THR_EVENT_U(0-3)` writer - The interrupt enable bit for the PCNT_CNT_THR_EVENT_U%s_INT interrupt."]
pub type CNT_THR_EVENT_U_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "The interrupt enable bit for the PCNT_CNT_THR_EVENT_U(0-3)_INT interrupt."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CNT_THR_EVENT_U0` field.</div>"]
    #[inline(always)]
    pub fn cnt_thr_event_u(&self, n: u8) -> CNT_THR_EVENT_U_R {
        #[allow(clippy::no_effect)]
        [(); 4][n as usize];
        CNT_THR_EVENT_U_R::new(((self.bits >> n) & 1) != 0)
    }
    #[doc = "Iterator for array of:"]
    #[doc = "The interrupt enable bit for the PCNT_CNT_THR_EVENT_U(0-3)_INT interrupt."]
    #[inline(always)]
    pub fn cnt_thr_event_u_iter(&self) -> impl Iterator<Item = CNT_THR_EVENT_U_R> + '_ {
        (0..4).map(move |n| CNT_THR_EVENT_U_R::new(((self.bits >> n) & 1) != 0))
    }
    #[doc = "Bit 0 - The interrupt enable bit for the PCNT_CNT_THR_EVENT_U0_INT interrupt."]
    #[inline(always)]
    pub fn cnt_thr_event_u0(&self) -> CNT_THR_EVENT_U_R {
        CNT_THR_EVENT_U_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The interrupt enable bit for the PCNT_CNT_THR_EVENT_U1_INT interrupt."]
    #[inline(always)]
    pub fn cnt_thr_event_u1(&self) -> CNT_THR_EVENT_U_R {
        CNT_THR_EVENT_U_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The interrupt enable bit for the PCNT_CNT_THR_EVENT_U2_INT interrupt."]
    #[inline(always)]
    pub fn cnt_thr_event_u2(&self) -> CNT_THR_EVENT_U_R {
        CNT_THR_EVENT_U_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The interrupt enable bit for the PCNT_CNT_THR_EVENT_U3_INT interrupt."]
    #[inline(always)]
    pub fn cnt_thr_event_u3(&self) -> CNT_THR_EVENT_U_R {
        CNT_THR_EVENT_U_R::new(((self.bits >> 3) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_ENA")
            .field("cnt_thr_event_u0", &self.cnt_thr_event_u0())
            .field("cnt_thr_event_u1", &self.cnt_thr_event_u1())
            .field("cnt_thr_event_u2", &self.cnt_thr_event_u2())
            .field("cnt_thr_event_u3", &self.cnt_thr_event_u3())
            .finish()
    }
}
impl W {
    #[doc = "The interrupt enable bit for the PCNT_CNT_THR_EVENT_U(0-3)_INT interrupt."]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is number of field in register. `n == 0` corresponds to `CNT_THR_EVENT_U0` field.</div>"]
    #[inline(always)]
    pub fn cnt_thr_event_u(&mut self, n: u8) -> CNT_THR_EVENT_U_W<'_, INT_ENA_SPEC> {
        #[allow(clippy::no_effect)]
        [(); 4][n as usize];
        CNT_THR_EVENT_U_W::new(self, n)
    }
    #[doc = "Bit 0 - The interrupt enable bit for the PCNT_CNT_THR_EVENT_U0_INT interrupt."]
    #[inline(always)]
    pub fn cnt_thr_event_u0(&mut self) -> CNT_THR_EVENT_U_W<'_, INT_ENA_SPEC> {
        CNT_THR_EVENT_U_W::new(self, 0)
    }
    #[doc = "Bit 1 - The interrupt enable bit for the PCNT_CNT_THR_EVENT_U1_INT interrupt."]
    #[inline(always)]
    pub fn cnt_thr_event_u1(&mut self) -> CNT_THR_EVENT_U_W<'_, INT_ENA_SPEC> {
        CNT_THR_EVENT_U_W::new(self, 1)
    }
    #[doc = "Bit 2 - The interrupt enable bit for the PCNT_CNT_THR_EVENT_U2_INT interrupt."]
    #[inline(always)]
    pub fn cnt_thr_event_u2(&mut self) -> CNT_THR_EVENT_U_W<'_, INT_ENA_SPEC> {
        CNT_THR_EVENT_U_W::new(self, 2)
    }
    #[doc = "Bit 3 - The interrupt enable bit for the PCNT_CNT_THR_EVENT_U3_INT interrupt."]
    #[inline(always)]
    pub fn cnt_thr_event_u3(&mut self) -> CNT_THR_EVENT_U_W<'_, INT_ENA_SPEC> {
        CNT_THR_EVENT_U_W::new(self, 3)
    }
}
#[doc = "Interrupt enable register\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
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
