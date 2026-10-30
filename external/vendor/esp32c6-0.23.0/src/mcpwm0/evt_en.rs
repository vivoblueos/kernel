#[doc = "Register `EVT_EN` reader"]
pub type R = crate::R<EVT_EN_SPEC>;
#[doc = "Register `EVT_EN` writer"]
pub type W = crate::W<EVT_EN_SPEC>;
#[doc = "Field `EVT_TIMER0_STOP_EN` reader - set this bit high to enable timer0 stop event generate"]
pub type EVT_TIMER0_STOP_EN_R = crate::BitReader;
#[doc = "Field `EVT_TIMER0_STOP_EN` writer - set this bit high to enable timer0 stop event generate"]
pub type EVT_TIMER0_STOP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TIMER1_STOP_EN` reader - set this bit high to enable timer1 stop event generate"]
pub type EVT_TIMER1_STOP_EN_R = crate::BitReader;
#[doc = "Field `EVT_TIMER1_STOP_EN` writer - set this bit high to enable timer1 stop event generate"]
pub type EVT_TIMER1_STOP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TIMER2_STOP_EN` reader - set this bit high to enable timer2 stop event generate"]
pub type EVT_TIMER2_STOP_EN_R = crate::BitReader;
#[doc = "Field `EVT_TIMER2_STOP_EN` writer - set this bit high to enable timer2 stop event generate"]
pub type EVT_TIMER2_STOP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TIMER0_TEZ_EN` reader - set this bit high to enable timer0 equal zero event generate"]
pub type EVT_TIMER0_TEZ_EN_R = crate::BitReader;
#[doc = "Field `EVT_TIMER0_TEZ_EN` writer - set this bit high to enable timer0 equal zero event generate"]
pub type EVT_TIMER0_TEZ_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TIMER1_TEZ_EN` reader - set this bit high to enable timer1 equal zero event generate"]
pub type EVT_TIMER1_TEZ_EN_R = crate::BitReader;
#[doc = "Field `EVT_TIMER1_TEZ_EN` writer - set this bit high to enable timer1 equal zero event generate"]
pub type EVT_TIMER1_TEZ_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TIMER2_TEZ_EN` reader - set this bit high to enable timer2 equal zero event generate"]
pub type EVT_TIMER2_TEZ_EN_R = crate::BitReader;
#[doc = "Field `EVT_TIMER2_TEZ_EN` writer - set this bit high to enable timer2 equal zero event generate"]
pub type EVT_TIMER2_TEZ_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TIMER0_TEP_EN` reader - set this bit high to enable timer0 equal period event generate"]
pub type EVT_TIMER0_TEP_EN_R = crate::BitReader;
#[doc = "Field `EVT_TIMER0_TEP_EN` writer - set this bit high to enable timer0 equal period event generate"]
pub type EVT_TIMER0_TEP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TIMER1_TEP_EN` reader - set this bit high to enable timer1 equal period event generate"]
pub type EVT_TIMER1_TEP_EN_R = crate::BitReader;
#[doc = "Field `EVT_TIMER1_TEP_EN` writer - set this bit high to enable timer1 equal period event generate"]
pub type EVT_TIMER1_TEP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TIMER2_TEP_EN` reader - set this bit high to enable timer2 equal period event generate"]
pub type EVT_TIMER2_TEP_EN_R = crate::BitReader;
#[doc = "Field `EVT_TIMER2_TEP_EN` writer - set this bit high to enable timer2 equal period event generate"]
pub type EVT_TIMER2_TEP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_OP0_TEA_EN` reader - set this bit high to enable PWM generator0 timer equal a event generate"]
pub type EVT_OP0_TEA_EN_R = crate::BitReader;
#[doc = "Field `EVT_OP0_TEA_EN` writer - set this bit high to enable PWM generator0 timer equal a event generate"]
pub type EVT_OP0_TEA_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_OP1_TEA_EN` reader - set this bit high to enable PWM generator1 timer equal a event generate"]
pub type EVT_OP1_TEA_EN_R = crate::BitReader;
#[doc = "Field `EVT_OP1_TEA_EN` writer - set this bit high to enable PWM generator1 timer equal a event generate"]
pub type EVT_OP1_TEA_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_OP2_TEA_EN` reader - set this bit high to enable PWM generator2 timer equal a event generate"]
pub type EVT_OP2_TEA_EN_R = crate::BitReader;
#[doc = "Field `EVT_OP2_TEA_EN` writer - set this bit high to enable PWM generator2 timer equal a event generate"]
pub type EVT_OP2_TEA_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_OP0_TEB_EN` reader - set this bit high to enable PWM generator0 timer equal b event generate"]
pub type EVT_OP0_TEB_EN_R = crate::BitReader;
#[doc = "Field `EVT_OP0_TEB_EN` writer - set this bit high to enable PWM generator0 timer equal b event generate"]
pub type EVT_OP0_TEB_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_OP1_TEB_EN` reader - set this bit high to enable PWM generator1 timer equal b event generate"]
pub type EVT_OP1_TEB_EN_R = crate::BitReader;
#[doc = "Field `EVT_OP1_TEB_EN` writer - set this bit high to enable PWM generator1 timer equal b event generate"]
pub type EVT_OP1_TEB_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_OP2_TEB_EN` reader - set this bit high to enable PWM generator2 timer equal b event generate"]
pub type EVT_OP2_TEB_EN_R = crate::BitReader;
#[doc = "Field `EVT_OP2_TEB_EN` writer - set this bit high to enable PWM generator2 timer equal b event generate"]
pub type EVT_OP2_TEB_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_F0_EN` reader - set this bit high to enable fault0 event generate"]
pub type EVT_F0_EN_R = crate::BitReader;
#[doc = "Field `EVT_F0_EN` writer - set this bit high to enable fault0 event generate"]
pub type EVT_F0_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_F1_EN` reader - set this bit high to enable fault1 event generate"]
pub type EVT_F1_EN_R = crate::BitReader;
#[doc = "Field `EVT_F1_EN` writer - set this bit high to enable fault1 event generate"]
pub type EVT_F1_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_F2_EN` reader - set this bit high to enable fault2 event generate"]
pub type EVT_F2_EN_R = crate::BitReader;
#[doc = "Field `EVT_F2_EN` writer - set this bit high to enable fault2 event generate"]
pub type EVT_F2_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_F0_CLR_EN` reader - set this bit high to enable fault0 clear event generate"]
pub type EVT_F0_CLR_EN_R = crate::BitReader;
#[doc = "Field `EVT_F0_CLR_EN` writer - set this bit high to enable fault0 clear event generate"]
pub type EVT_F0_CLR_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_F1_CLR_EN` reader - set this bit high to enable fault1 clear event generate"]
pub type EVT_F1_CLR_EN_R = crate::BitReader;
#[doc = "Field `EVT_F1_CLR_EN` writer - set this bit high to enable fault1 clear event generate"]
pub type EVT_F1_CLR_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_F2_CLR_EN` reader - set this bit high to enable fault2 clear event generate"]
pub type EVT_F2_CLR_EN_R = crate::BitReader;
#[doc = "Field `EVT_F2_CLR_EN` writer - set this bit high to enable fault2 clear event generate"]
pub type EVT_F2_CLR_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TZ0_CBC_EN` reader - set this bit high to enable cycle by cycle trip0 event generate"]
pub type EVT_TZ0_CBC_EN_R = crate::BitReader;
#[doc = "Field `EVT_TZ0_CBC_EN` writer - set this bit high to enable cycle by cycle trip0 event generate"]
pub type EVT_TZ0_CBC_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TZ1_CBC_EN` reader - set this bit high to enable cycle by cycle trip1 event generate"]
pub type EVT_TZ1_CBC_EN_R = crate::BitReader;
#[doc = "Field `EVT_TZ1_CBC_EN` writer - set this bit high to enable cycle by cycle trip1 event generate"]
pub type EVT_TZ1_CBC_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TZ2_CBC_EN` reader - set this bit high to enable cycle by cycle trip2 event generate"]
pub type EVT_TZ2_CBC_EN_R = crate::BitReader;
#[doc = "Field `EVT_TZ2_CBC_EN` writer - set this bit high to enable cycle by cycle trip2 event generate"]
pub type EVT_TZ2_CBC_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TZ0_OST_EN` reader - set this bit high to enable one shot trip0 event generate"]
pub type EVT_TZ0_OST_EN_R = crate::BitReader;
#[doc = "Field `EVT_TZ0_OST_EN` writer - set this bit high to enable one shot trip0 event generate"]
pub type EVT_TZ0_OST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TZ1_OST_EN` reader - set this bit high to enable one shot trip1 event generate"]
pub type EVT_TZ1_OST_EN_R = crate::BitReader;
#[doc = "Field `EVT_TZ1_OST_EN` writer - set this bit high to enable one shot trip1 event generate"]
pub type EVT_TZ1_OST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_TZ2_OST_EN` reader - set this bit high to enable one shot trip2 event generate"]
pub type EVT_TZ2_OST_EN_R = crate::BitReader;
#[doc = "Field `EVT_TZ2_OST_EN` writer - set this bit high to enable one shot trip2 event generate"]
pub type EVT_TZ2_OST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_CAP0_EN` reader - set this bit high to enable capture0 event generate"]
pub type EVT_CAP0_EN_R = crate::BitReader;
#[doc = "Field `EVT_CAP0_EN` writer - set this bit high to enable capture0 event generate"]
pub type EVT_CAP0_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_CAP1_EN` reader - set this bit high to enable capture1 event generate"]
pub type EVT_CAP1_EN_R = crate::BitReader;
#[doc = "Field `EVT_CAP1_EN` writer - set this bit high to enable capture1 event generate"]
pub type EVT_CAP1_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EVT_CAP2_EN` reader - set this bit high to enable capture2 event generate"]
pub type EVT_CAP2_EN_R = crate::BitReader;
#[doc = "Field `EVT_CAP2_EN` writer - set this bit high to enable capture2 event generate"]
pub type EVT_CAP2_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - set this bit high to enable timer0 stop event generate"]
    #[inline(always)]
    pub fn evt_timer0_stop_en(&self) -> EVT_TIMER0_STOP_EN_R {
        EVT_TIMER0_STOP_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - set this bit high to enable timer1 stop event generate"]
    #[inline(always)]
    pub fn evt_timer1_stop_en(&self) -> EVT_TIMER1_STOP_EN_R {
        EVT_TIMER1_STOP_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - set this bit high to enable timer2 stop event generate"]
    #[inline(always)]
    pub fn evt_timer2_stop_en(&self) -> EVT_TIMER2_STOP_EN_R {
        EVT_TIMER2_STOP_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - set this bit high to enable timer0 equal zero event generate"]
    #[inline(always)]
    pub fn evt_timer0_tez_en(&self) -> EVT_TIMER0_TEZ_EN_R {
        EVT_TIMER0_TEZ_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - set this bit high to enable timer1 equal zero event generate"]
    #[inline(always)]
    pub fn evt_timer1_tez_en(&self) -> EVT_TIMER1_TEZ_EN_R {
        EVT_TIMER1_TEZ_EN_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - set this bit high to enable timer2 equal zero event generate"]
    #[inline(always)]
    pub fn evt_timer2_tez_en(&self) -> EVT_TIMER2_TEZ_EN_R {
        EVT_TIMER2_TEZ_EN_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - set this bit high to enable timer0 equal period event generate"]
    #[inline(always)]
    pub fn evt_timer0_tep_en(&self) -> EVT_TIMER0_TEP_EN_R {
        EVT_TIMER0_TEP_EN_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - set this bit high to enable timer1 equal period event generate"]
    #[inline(always)]
    pub fn evt_timer1_tep_en(&self) -> EVT_TIMER1_TEP_EN_R {
        EVT_TIMER1_TEP_EN_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - set this bit high to enable timer2 equal period event generate"]
    #[inline(always)]
    pub fn evt_timer2_tep_en(&self) -> EVT_TIMER2_TEP_EN_R {
        EVT_TIMER2_TEP_EN_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - set this bit high to enable PWM generator0 timer equal a event generate"]
    #[inline(always)]
    pub fn evt_op0_tea_en(&self) -> EVT_OP0_TEA_EN_R {
        EVT_OP0_TEA_EN_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - set this bit high to enable PWM generator1 timer equal a event generate"]
    #[inline(always)]
    pub fn evt_op1_tea_en(&self) -> EVT_OP1_TEA_EN_R {
        EVT_OP1_TEA_EN_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - set this bit high to enable PWM generator2 timer equal a event generate"]
    #[inline(always)]
    pub fn evt_op2_tea_en(&self) -> EVT_OP2_TEA_EN_R {
        EVT_OP2_TEA_EN_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - set this bit high to enable PWM generator0 timer equal b event generate"]
    #[inline(always)]
    pub fn evt_op0_teb_en(&self) -> EVT_OP0_TEB_EN_R {
        EVT_OP0_TEB_EN_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - set this bit high to enable PWM generator1 timer equal b event generate"]
    #[inline(always)]
    pub fn evt_op1_teb_en(&self) -> EVT_OP1_TEB_EN_R {
        EVT_OP1_TEB_EN_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - set this bit high to enable PWM generator2 timer equal b event generate"]
    #[inline(always)]
    pub fn evt_op2_teb_en(&self) -> EVT_OP2_TEB_EN_R {
        EVT_OP2_TEB_EN_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - set this bit high to enable fault0 event generate"]
    #[inline(always)]
    pub fn evt_f0_en(&self) -> EVT_F0_EN_R {
        EVT_F0_EN_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - set this bit high to enable fault1 event generate"]
    #[inline(always)]
    pub fn evt_f1_en(&self) -> EVT_F1_EN_R {
        EVT_F1_EN_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - set this bit high to enable fault2 event generate"]
    #[inline(always)]
    pub fn evt_f2_en(&self) -> EVT_F2_EN_R {
        EVT_F2_EN_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - set this bit high to enable fault0 clear event generate"]
    #[inline(always)]
    pub fn evt_f0_clr_en(&self) -> EVT_F0_CLR_EN_R {
        EVT_F0_CLR_EN_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - set this bit high to enable fault1 clear event generate"]
    #[inline(always)]
    pub fn evt_f1_clr_en(&self) -> EVT_F1_CLR_EN_R {
        EVT_F1_CLR_EN_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - set this bit high to enable fault2 clear event generate"]
    #[inline(always)]
    pub fn evt_f2_clr_en(&self) -> EVT_F2_CLR_EN_R {
        EVT_F2_CLR_EN_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - set this bit high to enable cycle by cycle trip0 event generate"]
    #[inline(always)]
    pub fn evt_tz0_cbc_en(&self) -> EVT_TZ0_CBC_EN_R {
        EVT_TZ0_CBC_EN_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - set this bit high to enable cycle by cycle trip1 event generate"]
    #[inline(always)]
    pub fn evt_tz1_cbc_en(&self) -> EVT_TZ1_CBC_EN_R {
        EVT_TZ1_CBC_EN_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - set this bit high to enable cycle by cycle trip2 event generate"]
    #[inline(always)]
    pub fn evt_tz2_cbc_en(&self) -> EVT_TZ2_CBC_EN_R {
        EVT_TZ2_CBC_EN_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - set this bit high to enable one shot trip0 event generate"]
    #[inline(always)]
    pub fn evt_tz0_ost_en(&self) -> EVT_TZ0_OST_EN_R {
        EVT_TZ0_OST_EN_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - set this bit high to enable one shot trip1 event generate"]
    #[inline(always)]
    pub fn evt_tz1_ost_en(&self) -> EVT_TZ1_OST_EN_R {
        EVT_TZ1_OST_EN_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - set this bit high to enable one shot trip2 event generate"]
    #[inline(always)]
    pub fn evt_tz2_ost_en(&self) -> EVT_TZ2_OST_EN_R {
        EVT_TZ2_OST_EN_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - set this bit high to enable capture0 event generate"]
    #[inline(always)]
    pub fn evt_cap0_en(&self) -> EVT_CAP0_EN_R {
        EVT_CAP0_EN_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - set this bit high to enable capture1 event generate"]
    #[inline(always)]
    pub fn evt_cap1_en(&self) -> EVT_CAP1_EN_R {
        EVT_CAP1_EN_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - set this bit high to enable capture2 event generate"]
    #[inline(always)]
    pub fn evt_cap2_en(&self) -> EVT_CAP2_EN_R {
        EVT_CAP2_EN_R::new(((self.bits >> 29) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("EVT_EN")
            .field("evt_timer0_stop_en", &self.evt_timer0_stop_en())
            .field("evt_timer1_stop_en", &self.evt_timer1_stop_en())
            .field("evt_timer2_stop_en", &self.evt_timer2_stop_en())
            .field("evt_timer0_tez_en", &self.evt_timer0_tez_en())
            .field("evt_timer1_tez_en", &self.evt_timer1_tez_en())
            .field("evt_timer2_tez_en", &self.evt_timer2_tez_en())
            .field("evt_timer0_tep_en", &self.evt_timer0_tep_en())
            .field("evt_timer1_tep_en", &self.evt_timer1_tep_en())
            .field("evt_timer2_tep_en", &self.evt_timer2_tep_en())
            .field("evt_op0_tea_en", &self.evt_op0_tea_en())
            .field("evt_op1_tea_en", &self.evt_op1_tea_en())
            .field("evt_op2_tea_en", &self.evt_op2_tea_en())
            .field("evt_op0_teb_en", &self.evt_op0_teb_en())
            .field("evt_op1_teb_en", &self.evt_op1_teb_en())
            .field("evt_op2_teb_en", &self.evt_op2_teb_en())
            .field("evt_f0_en", &self.evt_f0_en())
            .field("evt_f1_en", &self.evt_f1_en())
            .field("evt_f2_en", &self.evt_f2_en())
            .field("evt_f0_clr_en", &self.evt_f0_clr_en())
            .field("evt_f1_clr_en", &self.evt_f1_clr_en())
            .field("evt_f2_clr_en", &self.evt_f2_clr_en())
            .field("evt_tz0_cbc_en", &self.evt_tz0_cbc_en())
            .field("evt_tz1_cbc_en", &self.evt_tz1_cbc_en())
            .field("evt_tz2_cbc_en", &self.evt_tz2_cbc_en())
            .field("evt_tz0_ost_en", &self.evt_tz0_ost_en())
            .field("evt_tz1_ost_en", &self.evt_tz1_ost_en())
            .field("evt_tz2_ost_en", &self.evt_tz2_ost_en())
            .field("evt_cap0_en", &self.evt_cap0_en())
            .field("evt_cap1_en", &self.evt_cap1_en())
            .field("evt_cap2_en", &self.evt_cap2_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - set this bit high to enable timer0 stop event generate"]
    #[inline(always)]
    pub fn evt_timer0_stop_en(&mut self) -> EVT_TIMER0_STOP_EN_W<'_, EVT_EN_SPEC> {
        EVT_TIMER0_STOP_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - set this bit high to enable timer1 stop event generate"]
    #[inline(always)]
    pub fn evt_timer1_stop_en(&mut self) -> EVT_TIMER1_STOP_EN_W<'_, EVT_EN_SPEC> {
        EVT_TIMER1_STOP_EN_W::new(self, 1)
    }
    #[doc = "Bit 2 - set this bit high to enable timer2 stop event generate"]
    #[inline(always)]
    pub fn evt_timer2_stop_en(&mut self) -> EVT_TIMER2_STOP_EN_W<'_, EVT_EN_SPEC> {
        EVT_TIMER2_STOP_EN_W::new(self, 2)
    }
    #[doc = "Bit 3 - set this bit high to enable timer0 equal zero event generate"]
    #[inline(always)]
    pub fn evt_timer0_tez_en(&mut self) -> EVT_TIMER0_TEZ_EN_W<'_, EVT_EN_SPEC> {
        EVT_TIMER0_TEZ_EN_W::new(self, 3)
    }
    #[doc = "Bit 4 - set this bit high to enable timer1 equal zero event generate"]
    #[inline(always)]
    pub fn evt_timer1_tez_en(&mut self) -> EVT_TIMER1_TEZ_EN_W<'_, EVT_EN_SPEC> {
        EVT_TIMER1_TEZ_EN_W::new(self, 4)
    }
    #[doc = "Bit 5 - set this bit high to enable timer2 equal zero event generate"]
    #[inline(always)]
    pub fn evt_timer2_tez_en(&mut self) -> EVT_TIMER2_TEZ_EN_W<'_, EVT_EN_SPEC> {
        EVT_TIMER2_TEZ_EN_W::new(self, 5)
    }
    #[doc = "Bit 6 - set this bit high to enable timer0 equal period event generate"]
    #[inline(always)]
    pub fn evt_timer0_tep_en(&mut self) -> EVT_TIMER0_TEP_EN_W<'_, EVT_EN_SPEC> {
        EVT_TIMER0_TEP_EN_W::new(self, 6)
    }
    #[doc = "Bit 7 - set this bit high to enable timer1 equal period event generate"]
    #[inline(always)]
    pub fn evt_timer1_tep_en(&mut self) -> EVT_TIMER1_TEP_EN_W<'_, EVT_EN_SPEC> {
        EVT_TIMER1_TEP_EN_W::new(self, 7)
    }
    #[doc = "Bit 8 - set this bit high to enable timer2 equal period event generate"]
    #[inline(always)]
    pub fn evt_timer2_tep_en(&mut self) -> EVT_TIMER2_TEP_EN_W<'_, EVT_EN_SPEC> {
        EVT_TIMER2_TEP_EN_W::new(self, 8)
    }
    #[doc = "Bit 9 - set this bit high to enable PWM generator0 timer equal a event generate"]
    #[inline(always)]
    pub fn evt_op0_tea_en(&mut self) -> EVT_OP0_TEA_EN_W<'_, EVT_EN_SPEC> {
        EVT_OP0_TEA_EN_W::new(self, 9)
    }
    #[doc = "Bit 10 - set this bit high to enable PWM generator1 timer equal a event generate"]
    #[inline(always)]
    pub fn evt_op1_tea_en(&mut self) -> EVT_OP1_TEA_EN_W<'_, EVT_EN_SPEC> {
        EVT_OP1_TEA_EN_W::new(self, 10)
    }
    #[doc = "Bit 11 - set this bit high to enable PWM generator2 timer equal a event generate"]
    #[inline(always)]
    pub fn evt_op2_tea_en(&mut self) -> EVT_OP2_TEA_EN_W<'_, EVT_EN_SPEC> {
        EVT_OP2_TEA_EN_W::new(self, 11)
    }
    #[doc = "Bit 12 - set this bit high to enable PWM generator0 timer equal b event generate"]
    #[inline(always)]
    pub fn evt_op0_teb_en(&mut self) -> EVT_OP0_TEB_EN_W<'_, EVT_EN_SPEC> {
        EVT_OP0_TEB_EN_W::new(self, 12)
    }
    #[doc = "Bit 13 - set this bit high to enable PWM generator1 timer equal b event generate"]
    #[inline(always)]
    pub fn evt_op1_teb_en(&mut self) -> EVT_OP1_TEB_EN_W<'_, EVT_EN_SPEC> {
        EVT_OP1_TEB_EN_W::new(self, 13)
    }
    #[doc = "Bit 14 - set this bit high to enable PWM generator2 timer equal b event generate"]
    #[inline(always)]
    pub fn evt_op2_teb_en(&mut self) -> EVT_OP2_TEB_EN_W<'_, EVT_EN_SPEC> {
        EVT_OP2_TEB_EN_W::new(self, 14)
    }
    #[doc = "Bit 15 - set this bit high to enable fault0 event generate"]
    #[inline(always)]
    pub fn evt_f0_en(&mut self) -> EVT_F0_EN_W<'_, EVT_EN_SPEC> {
        EVT_F0_EN_W::new(self, 15)
    }
    #[doc = "Bit 16 - set this bit high to enable fault1 event generate"]
    #[inline(always)]
    pub fn evt_f1_en(&mut self) -> EVT_F1_EN_W<'_, EVT_EN_SPEC> {
        EVT_F1_EN_W::new(self, 16)
    }
    #[doc = "Bit 17 - set this bit high to enable fault2 event generate"]
    #[inline(always)]
    pub fn evt_f2_en(&mut self) -> EVT_F2_EN_W<'_, EVT_EN_SPEC> {
        EVT_F2_EN_W::new(self, 17)
    }
    #[doc = "Bit 18 - set this bit high to enable fault0 clear event generate"]
    #[inline(always)]
    pub fn evt_f0_clr_en(&mut self) -> EVT_F0_CLR_EN_W<'_, EVT_EN_SPEC> {
        EVT_F0_CLR_EN_W::new(self, 18)
    }
    #[doc = "Bit 19 - set this bit high to enable fault1 clear event generate"]
    #[inline(always)]
    pub fn evt_f1_clr_en(&mut self) -> EVT_F1_CLR_EN_W<'_, EVT_EN_SPEC> {
        EVT_F1_CLR_EN_W::new(self, 19)
    }
    #[doc = "Bit 20 - set this bit high to enable fault2 clear event generate"]
    #[inline(always)]
    pub fn evt_f2_clr_en(&mut self) -> EVT_F2_CLR_EN_W<'_, EVT_EN_SPEC> {
        EVT_F2_CLR_EN_W::new(self, 20)
    }
    #[doc = "Bit 21 - set this bit high to enable cycle by cycle trip0 event generate"]
    #[inline(always)]
    pub fn evt_tz0_cbc_en(&mut self) -> EVT_TZ0_CBC_EN_W<'_, EVT_EN_SPEC> {
        EVT_TZ0_CBC_EN_W::new(self, 21)
    }
    #[doc = "Bit 22 - set this bit high to enable cycle by cycle trip1 event generate"]
    #[inline(always)]
    pub fn evt_tz1_cbc_en(&mut self) -> EVT_TZ1_CBC_EN_W<'_, EVT_EN_SPEC> {
        EVT_TZ1_CBC_EN_W::new(self, 22)
    }
    #[doc = "Bit 23 - set this bit high to enable cycle by cycle trip2 event generate"]
    #[inline(always)]
    pub fn evt_tz2_cbc_en(&mut self) -> EVT_TZ2_CBC_EN_W<'_, EVT_EN_SPEC> {
        EVT_TZ2_CBC_EN_W::new(self, 23)
    }
    #[doc = "Bit 24 - set this bit high to enable one shot trip0 event generate"]
    #[inline(always)]
    pub fn evt_tz0_ost_en(&mut self) -> EVT_TZ0_OST_EN_W<'_, EVT_EN_SPEC> {
        EVT_TZ0_OST_EN_W::new(self, 24)
    }
    #[doc = "Bit 25 - set this bit high to enable one shot trip1 event generate"]
    #[inline(always)]
    pub fn evt_tz1_ost_en(&mut self) -> EVT_TZ1_OST_EN_W<'_, EVT_EN_SPEC> {
        EVT_TZ1_OST_EN_W::new(self, 25)
    }
    #[doc = "Bit 26 - set this bit high to enable one shot trip2 event generate"]
    #[inline(always)]
    pub fn evt_tz2_ost_en(&mut self) -> EVT_TZ2_OST_EN_W<'_, EVT_EN_SPEC> {
        EVT_TZ2_OST_EN_W::new(self, 26)
    }
    #[doc = "Bit 27 - set this bit high to enable capture0 event generate"]
    #[inline(always)]
    pub fn evt_cap0_en(&mut self) -> EVT_CAP0_EN_W<'_, EVT_EN_SPEC> {
        EVT_CAP0_EN_W::new(self, 27)
    }
    #[doc = "Bit 28 - set this bit high to enable capture1 event generate"]
    #[inline(always)]
    pub fn evt_cap1_en(&mut self) -> EVT_CAP1_EN_W<'_, EVT_EN_SPEC> {
        EVT_CAP1_EN_W::new(self, 28)
    }
    #[doc = "Bit 29 - set this bit high to enable capture2 event generate"]
    #[inline(always)]
    pub fn evt_cap2_en(&mut self) -> EVT_CAP2_EN_W<'_, EVT_EN_SPEC> {
        EVT_CAP2_EN_W::new(self, 29)
    }
}
#[doc = "MCPWM event enable register\n\nYou can [`read`](crate::Reg::read) this register and get [`evt_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`evt_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct EVT_EN_SPEC;
impl crate::RegisterSpec for EVT_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`evt_en::R`](R) reader structure"]
impl crate::Readable for EVT_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`evt_en::W`](W) writer structure"]
impl crate::Writable for EVT_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets EVT_EN to value 0"]
impl crate::Resettable for EVT_EN_SPEC {}
