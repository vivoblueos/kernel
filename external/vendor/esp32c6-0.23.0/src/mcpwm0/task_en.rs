#[doc = "Register `TASK_EN` reader"]
pub type R = crate::R<TASK_EN_SPEC>;
#[doc = "Register `TASK_EN` writer"]
pub type W = crate::W<TASK_EN_SPEC>;
#[doc = "Field `TASK_CMPR0_A_UP_EN` reader - set this bit high to enable PWM generator0 timer stamp A's shadow register update task receive"]
pub type TASK_CMPR0_A_UP_EN_R = crate::BitReader;
#[doc = "Field `TASK_CMPR0_A_UP_EN` writer - set this bit high to enable PWM generator0 timer stamp A's shadow register update task receive"]
pub type TASK_CMPR0_A_UP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_CMPR1_A_UP_EN` reader - set this bit high to enable PWM generator1 timer stamp A's shadow register update task receive"]
pub type TASK_CMPR1_A_UP_EN_R = crate::BitReader;
#[doc = "Field `TASK_CMPR1_A_UP_EN` writer - set this bit high to enable PWM generator1 timer stamp A's shadow register update task receive"]
pub type TASK_CMPR1_A_UP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_CMPR2_A_UP_EN` reader - set this bit high to enable PWM generator2 timer stamp A's shadow register update task receive"]
pub type TASK_CMPR2_A_UP_EN_R = crate::BitReader;
#[doc = "Field `TASK_CMPR2_A_UP_EN` writer - set this bit high to enable PWM generator2 timer stamp A's shadow register update task receive"]
pub type TASK_CMPR2_A_UP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_CMPR0_B_UP_EN` reader - set this bit high to enable PWM generator0 timer stamp B's shadow register update task receive"]
pub type TASK_CMPR0_B_UP_EN_R = crate::BitReader;
#[doc = "Field `TASK_CMPR0_B_UP_EN` writer - set this bit high to enable PWM generator0 timer stamp B's shadow register update task receive"]
pub type TASK_CMPR0_B_UP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_CMPR1_B_UP_EN` reader - set this bit high to enable PWM generator1 timer stamp B's shadow register update task receive"]
pub type TASK_CMPR1_B_UP_EN_R = crate::BitReader;
#[doc = "Field `TASK_CMPR1_B_UP_EN` writer - set this bit high to enable PWM generator1 timer stamp B's shadow register update task receive"]
pub type TASK_CMPR1_B_UP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_CMPR2_B_UP_EN` reader - set this bit high to enable PWM generator2 timer stamp B's shadow register update task receive"]
pub type TASK_CMPR2_B_UP_EN_R = crate::BitReader;
#[doc = "Field `TASK_CMPR2_B_UP_EN` writer - set this bit high to enable PWM generator2 timer stamp B's shadow register update task receive"]
pub type TASK_CMPR2_B_UP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_GEN_STOP_EN` reader - set this bit high to enable all PWM generate stop task receive"]
pub type TASK_GEN_STOP_EN_R = crate::BitReader;
#[doc = "Field `TASK_GEN_STOP_EN` writer - set this bit high to enable all PWM generate stop task receive"]
pub type TASK_GEN_STOP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_TIMER0_SYNC_EN` reader - set this bit high to enable timer0 sync task receive"]
pub type TASK_TIMER0_SYNC_EN_R = crate::BitReader;
#[doc = "Field `TASK_TIMER0_SYNC_EN` writer - set this bit high to enable timer0 sync task receive"]
pub type TASK_TIMER0_SYNC_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_TIMER1_SYNC_EN` reader - set this bit high to enable timer1 sync task receive"]
pub type TASK_TIMER1_SYNC_EN_R = crate::BitReader;
#[doc = "Field `TASK_TIMER1_SYNC_EN` writer - set this bit high to enable timer1 sync task receive"]
pub type TASK_TIMER1_SYNC_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_TIMER2_SYNC_EN` reader - set this bit high to enable timer2 sync task receive"]
pub type TASK_TIMER2_SYNC_EN_R = crate::BitReader;
#[doc = "Field `TASK_TIMER2_SYNC_EN` writer - set this bit high to enable timer2 sync task receive"]
pub type TASK_TIMER2_SYNC_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_TIMER0_PERIOD_UP_EN` reader - set this bit high to enable timer0 period update task receive"]
pub type TASK_TIMER0_PERIOD_UP_EN_R = crate::BitReader;
#[doc = "Field `TASK_TIMER0_PERIOD_UP_EN` writer - set this bit high to enable timer0 period update task receive"]
pub type TASK_TIMER0_PERIOD_UP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_TIMER1_PERIOD_UP_EN` reader - set this bit high to enable timer1 period update task receive"]
pub type TASK_TIMER1_PERIOD_UP_EN_R = crate::BitReader;
#[doc = "Field `TASK_TIMER1_PERIOD_UP_EN` writer - set this bit high to enable timer1 period update task receive"]
pub type TASK_TIMER1_PERIOD_UP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_TIMER2_PERIOD_UP_EN` reader - set this bit high to enable timer2 period update task receive"]
pub type TASK_TIMER2_PERIOD_UP_EN_R = crate::BitReader;
#[doc = "Field `TASK_TIMER2_PERIOD_UP_EN` writer - set this bit high to enable timer2 period update task receive"]
pub type TASK_TIMER2_PERIOD_UP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_TZ0_OST_EN` reader - set this bit high to enable one shot trip0 task receive"]
pub type TASK_TZ0_OST_EN_R = crate::BitReader;
#[doc = "Field `TASK_TZ0_OST_EN` writer - set this bit high to enable one shot trip0 task receive"]
pub type TASK_TZ0_OST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_TZ1_OST_EN` reader - set this bit high to enable one shot trip1 task receive"]
pub type TASK_TZ1_OST_EN_R = crate::BitReader;
#[doc = "Field `TASK_TZ1_OST_EN` writer - set this bit high to enable one shot trip1 task receive"]
pub type TASK_TZ1_OST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_TZ2_OST_EN` reader - set this bit high to enable one shot trip2 task receive"]
pub type TASK_TZ2_OST_EN_R = crate::BitReader;
#[doc = "Field `TASK_TZ2_OST_EN` writer - set this bit high to enable one shot trip2 task receive"]
pub type TASK_TZ2_OST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_CLR0_OST_EN` reader - set this bit high to enable one shot trip0 clear task receive"]
pub type TASK_CLR0_OST_EN_R = crate::BitReader;
#[doc = "Field `TASK_CLR0_OST_EN` writer - set this bit high to enable one shot trip0 clear task receive"]
pub type TASK_CLR0_OST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_CLR1_OST_EN` reader - set this bit high to enable one shot trip1 clear task receive"]
pub type TASK_CLR1_OST_EN_R = crate::BitReader;
#[doc = "Field `TASK_CLR1_OST_EN` writer - set this bit high to enable one shot trip1 clear task receive"]
pub type TASK_CLR1_OST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_CLR2_OST_EN` reader - set this bit high to enable one shot trip2 clear task receive"]
pub type TASK_CLR2_OST_EN_R = crate::BitReader;
#[doc = "Field `TASK_CLR2_OST_EN` writer - set this bit high to enable one shot trip2 clear task receive"]
pub type TASK_CLR2_OST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_CAP0_EN` reader - set this bit high to enable capture0 task receive"]
pub type TASK_CAP0_EN_R = crate::BitReader;
#[doc = "Field `TASK_CAP0_EN` writer - set this bit high to enable capture0 task receive"]
pub type TASK_CAP0_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_CAP1_EN` reader - set this bit high to enable capture1 task receive"]
pub type TASK_CAP1_EN_R = crate::BitReader;
#[doc = "Field `TASK_CAP1_EN` writer - set this bit high to enable capture1 task receive"]
pub type TASK_CAP1_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TASK_CAP2_EN` reader - set this bit high to enable capture2 task receive"]
pub type TASK_CAP2_EN_R = crate::BitReader;
#[doc = "Field `TASK_CAP2_EN` writer - set this bit high to enable capture2 task receive"]
pub type TASK_CAP2_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - set this bit high to enable PWM generator0 timer stamp A's shadow register update task receive"]
    #[inline(always)]
    pub fn task_cmpr0_a_up_en(&self) -> TASK_CMPR0_A_UP_EN_R {
        TASK_CMPR0_A_UP_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - set this bit high to enable PWM generator1 timer stamp A's shadow register update task receive"]
    #[inline(always)]
    pub fn task_cmpr1_a_up_en(&self) -> TASK_CMPR1_A_UP_EN_R {
        TASK_CMPR1_A_UP_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - set this bit high to enable PWM generator2 timer stamp A's shadow register update task receive"]
    #[inline(always)]
    pub fn task_cmpr2_a_up_en(&self) -> TASK_CMPR2_A_UP_EN_R {
        TASK_CMPR2_A_UP_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - set this bit high to enable PWM generator0 timer stamp B's shadow register update task receive"]
    #[inline(always)]
    pub fn task_cmpr0_b_up_en(&self) -> TASK_CMPR0_B_UP_EN_R {
        TASK_CMPR0_B_UP_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - set this bit high to enable PWM generator1 timer stamp B's shadow register update task receive"]
    #[inline(always)]
    pub fn task_cmpr1_b_up_en(&self) -> TASK_CMPR1_B_UP_EN_R {
        TASK_CMPR1_B_UP_EN_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - set this bit high to enable PWM generator2 timer stamp B's shadow register update task receive"]
    #[inline(always)]
    pub fn task_cmpr2_b_up_en(&self) -> TASK_CMPR2_B_UP_EN_R {
        TASK_CMPR2_B_UP_EN_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - set this bit high to enable all PWM generate stop task receive"]
    #[inline(always)]
    pub fn task_gen_stop_en(&self) -> TASK_GEN_STOP_EN_R {
        TASK_GEN_STOP_EN_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - set this bit high to enable timer0 sync task receive"]
    #[inline(always)]
    pub fn task_timer0_sync_en(&self) -> TASK_TIMER0_SYNC_EN_R {
        TASK_TIMER0_SYNC_EN_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - set this bit high to enable timer1 sync task receive"]
    #[inline(always)]
    pub fn task_timer1_sync_en(&self) -> TASK_TIMER1_SYNC_EN_R {
        TASK_TIMER1_SYNC_EN_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - set this bit high to enable timer2 sync task receive"]
    #[inline(always)]
    pub fn task_timer2_sync_en(&self) -> TASK_TIMER2_SYNC_EN_R {
        TASK_TIMER2_SYNC_EN_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - set this bit high to enable timer0 period update task receive"]
    #[inline(always)]
    pub fn task_timer0_period_up_en(&self) -> TASK_TIMER0_PERIOD_UP_EN_R {
        TASK_TIMER0_PERIOD_UP_EN_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - set this bit high to enable timer1 period update task receive"]
    #[inline(always)]
    pub fn task_timer1_period_up_en(&self) -> TASK_TIMER1_PERIOD_UP_EN_R {
        TASK_TIMER1_PERIOD_UP_EN_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - set this bit high to enable timer2 period update task receive"]
    #[inline(always)]
    pub fn task_timer2_period_up_en(&self) -> TASK_TIMER2_PERIOD_UP_EN_R {
        TASK_TIMER2_PERIOD_UP_EN_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - set this bit high to enable one shot trip0 task receive"]
    #[inline(always)]
    pub fn task_tz0_ost_en(&self) -> TASK_TZ0_OST_EN_R {
        TASK_TZ0_OST_EN_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - set this bit high to enable one shot trip1 task receive"]
    #[inline(always)]
    pub fn task_tz1_ost_en(&self) -> TASK_TZ1_OST_EN_R {
        TASK_TZ1_OST_EN_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - set this bit high to enable one shot trip2 task receive"]
    #[inline(always)]
    pub fn task_tz2_ost_en(&self) -> TASK_TZ2_OST_EN_R {
        TASK_TZ2_OST_EN_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - set this bit high to enable one shot trip0 clear task receive"]
    #[inline(always)]
    pub fn task_clr0_ost_en(&self) -> TASK_CLR0_OST_EN_R {
        TASK_CLR0_OST_EN_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - set this bit high to enable one shot trip1 clear task receive"]
    #[inline(always)]
    pub fn task_clr1_ost_en(&self) -> TASK_CLR1_OST_EN_R {
        TASK_CLR1_OST_EN_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - set this bit high to enable one shot trip2 clear task receive"]
    #[inline(always)]
    pub fn task_clr2_ost_en(&self) -> TASK_CLR2_OST_EN_R {
        TASK_CLR2_OST_EN_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - set this bit high to enable capture0 task receive"]
    #[inline(always)]
    pub fn task_cap0_en(&self) -> TASK_CAP0_EN_R {
        TASK_CAP0_EN_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - set this bit high to enable capture1 task receive"]
    #[inline(always)]
    pub fn task_cap1_en(&self) -> TASK_CAP1_EN_R {
        TASK_CAP1_EN_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - set this bit high to enable capture2 task receive"]
    #[inline(always)]
    pub fn task_cap2_en(&self) -> TASK_CAP2_EN_R {
        TASK_CAP2_EN_R::new(((self.bits >> 21) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TASK_EN")
            .field("task_cmpr0_a_up_en", &self.task_cmpr0_a_up_en())
            .field("task_cmpr1_a_up_en", &self.task_cmpr1_a_up_en())
            .field("task_cmpr2_a_up_en", &self.task_cmpr2_a_up_en())
            .field("task_cmpr0_b_up_en", &self.task_cmpr0_b_up_en())
            .field("task_cmpr1_b_up_en", &self.task_cmpr1_b_up_en())
            .field("task_cmpr2_b_up_en", &self.task_cmpr2_b_up_en())
            .field("task_gen_stop_en", &self.task_gen_stop_en())
            .field("task_timer0_sync_en", &self.task_timer0_sync_en())
            .field("task_timer1_sync_en", &self.task_timer1_sync_en())
            .field("task_timer2_sync_en", &self.task_timer2_sync_en())
            .field("task_timer0_period_up_en", &self.task_timer0_period_up_en())
            .field("task_timer1_period_up_en", &self.task_timer1_period_up_en())
            .field("task_timer2_period_up_en", &self.task_timer2_period_up_en())
            .field("task_tz0_ost_en", &self.task_tz0_ost_en())
            .field("task_tz1_ost_en", &self.task_tz1_ost_en())
            .field("task_tz2_ost_en", &self.task_tz2_ost_en())
            .field("task_clr0_ost_en", &self.task_clr0_ost_en())
            .field("task_clr1_ost_en", &self.task_clr1_ost_en())
            .field("task_clr2_ost_en", &self.task_clr2_ost_en())
            .field("task_cap0_en", &self.task_cap0_en())
            .field("task_cap1_en", &self.task_cap1_en())
            .field("task_cap2_en", &self.task_cap2_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - set this bit high to enable PWM generator0 timer stamp A's shadow register update task receive"]
    #[inline(always)]
    pub fn task_cmpr0_a_up_en(&mut self) -> TASK_CMPR0_A_UP_EN_W<'_, TASK_EN_SPEC> {
        TASK_CMPR0_A_UP_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - set this bit high to enable PWM generator1 timer stamp A's shadow register update task receive"]
    #[inline(always)]
    pub fn task_cmpr1_a_up_en(&mut self) -> TASK_CMPR1_A_UP_EN_W<'_, TASK_EN_SPEC> {
        TASK_CMPR1_A_UP_EN_W::new(self, 1)
    }
    #[doc = "Bit 2 - set this bit high to enable PWM generator2 timer stamp A's shadow register update task receive"]
    #[inline(always)]
    pub fn task_cmpr2_a_up_en(&mut self) -> TASK_CMPR2_A_UP_EN_W<'_, TASK_EN_SPEC> {
        TASK_CMPR2_A_UP_EN_W::new(self, 2)
    }
    #[doc = "Bit 3 - set this bit high to enable PWM generator0 timer stamp B's shadow register update task receive"]
    #[inline(always)]
    pub fn task_cmpr0_b_up_en(&mut self) -> TASK_CMPR0_B_UP_EN_W<'_, TASK_EN_SPEC> {
        TASK_CMPR0_B_UP_EN_W::new(self, 3)
    }
    #[doc = "Bit 4 - set this bit high to enable PWM generator1 timer stamp B's shadow register update task receive"]
    #[inline(always)]
    pub fn task_cmpr1_b_up_en(&mut self) -> TASK_CMPR1_B_UP_EN_W<'_, TASK_EN_SPEC> {
        TASK_CMPR1_B_UP_EN_W::new(self, 4)
    }
    #[doc = "Bit 5 - set this bit high to enable PWM generator2 timer stamp B's shadow register update task receive"]
    #[inline(always)]
    pub fn task_cmpr2_b_up_en(&mut self) -> TASK_CMPR2_B_UP_EN_W<'_, TASK_EN_SPEC> {
        TASK_CMPR2_B_UP_EN_W::new(self, 5)
    }
    #[doc = "Bit 6 - set this bit high to enable all PWM generate stop task receive"]
    #[inline(always)]
    pub fn task_gen_stop_en(&mut self) -> TASK_GEN_STOP_EN_W<'_, TASK_EN_SPEC> {
        TASK_GEN_STOP_EN_W::new(self, 6)
    }
    #[doc = "Bit 7 - set this bit high to enable timer0 sync task receive"]
    #[inline(always)]
    pub fn task_timer0_sync_en(&mut self) -> TASK_TIMER0_SYNC_EN_W<'_, TASK_EN_SPEC> {
        TASK_TIMER0_SYNC_EN_W::new(self, 7)
    }
    #[doc = "Bit 8 - set this bit high to enable timer1 sync task receive"]
    #[inline(always)]
    pub fn task_timer1_sync_en(&mut self) -> TASK_TIMER1_SYNC_EN_W<'_, TASK_EN_SPEC> {
        TASK_TIMER1_SYNC_EN_W::new(self, 8)
    }
    #[doc = "Bit 9 - set this bit high to enable timer2 sync task receive"]
    #[inline(always)]
    pub fn task_timer2_sync_en(&mut self) -> TASK_TIMER2_SYNC_EN_W<'_, TASK_EN_SPEC> {
        TASK_TIMER2_SYNC_EN_W::new(self, 9)
    }
    #[doc = "Bit 10 - set this bit high to enable timer0 period update task receive"]
    #[inline(always)]
    pub fn task_timer0_period_up_en(&mut self) -> TASK_TIMER0_PERIOD_UP_EN_W<'_, TASK_EN_SPEC> {
        TASK_TIMER0_PERIOD_UP_EN_W::new(self, 10)
    }
    #[doc = "Bit 11 - set this bit high to enable timer1 period update task receive"]
    #[inline(always)]
    pub fn task_timer1_period_up_en(&mut self) -> TASK_TIMER1_PERIOD_UP_EN_W<'_, TASK_EN_SPEC> {
        TASK_TIMER1_PERIOD_UP_EN_W::new(self, 11)
    }
    #[doc = "Bit 12 - set this bit high to enable timer2 period update task receive"]
    #[inline(always)]
    pub fn task_timer2_period_up_en(&mut self) -> TASK_TIMER2_PERIOD_UP_EN_W<'_, TASK_EN_SPEC> {
        TASK_TIMER2_PERIOD_UP_EN_W::new(self, 12)
    }
    #[doc = "Bit 13 - set this bit high to enable one shot trip0 task receive"]
    #[inline(always)]
    pub fn task_tz0_ost_en(&mut self) -> TASK_TZ0_OST_EN_W<'_, TASK_EN_SPEC> {
        TASK_TZ0_OST_EN_W::new(self, 13)
    }
    #[doc = "Bit 14 - set this bit high to enable one shot trip1 task receive"]
    #[inline(always)]
    pub fn task_tz1_ost_en(&mut self) -> TASK_TZ1_OST_EN_W<'_, TASK_EN_SPEC> {
        TASK_TZ1_OST_EN_W::new(self, 14)
    }
    #[doc = "Bit 15 - set this bit high to enable one shot trip2 task receive"]
    #[inline(always)]
    pub fn task_tz2_ost_en(&mut self) -> TASK_TZ2_OST_EN_W<'_, TASK_EN_SPEC> {
        TASK_TZ2_OST_EN_W::new(self, 15)
    }
    #[doc = "Bit 16 - set this bit high to enable one shot trip0 clear task receive"]
    #[inline(always)]
    pub fn task_clr0_ost_en(&mut self) -> TASK_CLR0_OST_EN_W<'_, TASK_EN_SPEC> {
        TASK_CLR0_OST_EN_W::new(self, 16)
    }
    #[doc = "Bit 17 - set this bit high to enable one shot trip1 clear task receive"]
    #[inline(always)]
    pub fn task_clr1_ost_en(&mut self) -> TASK_CLR1_OST_EN_W<'_, TASK_EN_SPEC> {
        TASK_CLR1_OST_EN_W::new(self, 17)
    }
    #[doc = "Bit 18 - set this bit high to enable one shot trip2 clear task receive"]
    #[inline(always)]
    pub fn task_clr2_ost_en(&mut self) -> TASK_CLR2_OST_EN_W<'_, TASK_EN_SPEC> {
        TASK_CLR2_OST_EN_W::new(self, 18)
    }
    #[doc = "Bit 19 - set this bit high to enable capture0 task receive"]
    #[inline(always)]
    pub fn task_cap0_en(&mut self) -> TASK_CAP0_EN_W<'_, TASK_EN_SPEC> {
        TASK_CAP0_EN_W::new(self, 19)
    }
    #[doc = "Bit 20 - set this bit high to enable capture1 task receive"]
    #[inline(always)]
    pub fn task_cap1_en(&mut self) -> TASK_CAP1_EN_W<'_, TASK_EN_SPEC> {
        TASK_CAP1_EN_W::new(self, 20)
    }
    #[doc = "Bit 21 - set this bit high to enable capture2 task receive"]
    #[inline(always)]
    pub fn task_cap2_en(&mut self) -> TASK_CAP2_EN_W<'_, TASK_EN_SPEC> {
        TASK_CAP2_EN_W::new(self, 21)
    }
}
#[doc = "MCPWM task enable register\n\nYou can [`read`](crate::Reg::read) this register and get [`task_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`task_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TASK_EN_SPEC;
impl crate::RegisterSpec for TASK_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`task_en::R`](R) reader structure"]
impl crate::Readable for TASK_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`task_en::W`](W) writer structure"]
impl crate::Writable for TASK_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TASK_EN to value 0"]
impl crate::Resettable for TASK_EN_SPEC {}
