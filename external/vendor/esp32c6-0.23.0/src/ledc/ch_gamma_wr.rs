#[doc = "Register `CH%s_GAMMA_WR` reader"]
pub type R = crate::R<CH_GAMMA_WR_SPEC>;
#[doc = "Register `CH%s_GAMMA_WR` writer"]
pub type W = crate::W<CH_GAMMA_WR_SPEC>;
#[doc = "Field `CH_GAMMA_DUTY_INC` reader - Ledc ch%s gamma duty inc of current ram write address.This register is used to increase or decrease the duty of output signal on channel %s. 1: Increase 0: Decrease."]
pub type CH_GAMMA_DUTY_INC_R = crate::BitReader;
#[doc = "Field `CH_GAMMA_DUTY_INC` writer - Ledc ch%s gamma duty inc of current ram write address.This register is used to increase or decrease the duty of output signal on channel %s. 1: Increase 0: Decrease."]
pub type CH_GAMMA_DUTY_INC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH_GAMMA_DUTY_CYCLE` reader - Ledc ch%s gamma duty cycle of current ram write address.The duty will change every LEDC_CH%s_GAMMA_DUTY_CYCLE on channel %s."]
pub type CH_GAMMA_DUTY_CYCLE_R = crate::FieldReader<u16>;
#[doc = "Field `CH_GAMMA_DUTY_CYCLE` writer - Ledc ch%s gamma duty cycle of current ram write address.The duty will change every LEDC_CH%s_GAMMA_DUTY_CYCLE on channel %s."]
pub type CH_GAMMA_DUTY_CYCLE_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `CH_GAMMA_SCALE` reader - Ledc ch%s gamma scale of current ram write address.This register is used to configure the changing step scale of duty on channel %s."]
pub type CH_GAMMA_SCALE_R = crate::FieldReader<u16>;
#[doc = "Field `CH_GAMMA_SCALE` writer - Ledc ch%s gamma scale of current ram write address.This register is used to configure the changing step scale of duty on channel %s."]
pub type CH_GAMMA_SCALE_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `CH_GAMMA_DUTY_NUM` reader - Ledc ch%s gamma duty num of current ram write address.This register is used to control the number of times the duty cycle will be changed."]
pub type CH_GAMMA_DUTY_NUM_R = crate::FieldReader<u16>;
#[doc = "Field `CH_GAMMA_DUTY_NUM` writer - Ledc ch%s gamma duty num of current ram write address.This register is used to control the number of times the duty cycle will be changed."]
pub type CH_GAMMA_DUTY_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
impl R {
    #[doc = "Bit 0 - Ledc ch%s gamma duty inc of current ram write address.This register is used to increase or decrease the duty of output signal on channel %s. 1: Increase 0: Decrease."]
    #[inline(always)]
    pub fn ch_gamma_duty_inc(&self) -> CH_GAMMA_DUTY_INC_R {
        CH_GAMMA_DUTY_INC_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:10 - Ledc ch%s gamma duty cycle of current ram write address.The duty will change every LEDC_CH%s_GAMMA_DUTY_CYCLE on channel %s."]
    #[inline(always)]
    pub fn ch_gamma_duty_cycle(&self) -> CH_GAMMA_DUTY_CYCLE_R {
        CH_GAMMA_DUTY_CYCLE_R::new(((self.bits >> 1) & 0x03ff) as u16)
    }
    #[doc = "Bits 11:20 - Ledc ch%s gamma scale of current ram write address.This register is used to configure the changing step scale of duty on channel %s."]
    #[inline(always)]
    pub fn ch_gamma_scale(&self) -> CH_GAMMA_SCALE_R {
        CH_GAMMA_SCALE_R::new(((self.bits >> 11) & 0x03ff) as u16)
    }
    #[doc = "Bits 21:30 - Ledc ch%s gamma duty num of current ram write address.This register is used to control the number of times the duty cycle will be changed."]
    #[inline(always)]
    pub fn ch_gamma_duty_num(&self) -> CH_GAMMA_DUTY_NUM_R {
        CH_GAMMA_DUTY_NUM_R::new(((self.bits >> 21) & 0x03ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CH_GAMMA_WR")
            .field("ch_gamma_duty_inc", &self.ch_gamma_duty_inc())
            .field("ch_gamma_duty_cycle", &self.ch_gamma_duty_cycle())
            .field("ch_gamma_scale", &self.ch_gamma_scale())
            .field("ch_gamma_duty_num", &self.ch_gamma_duty_num())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Ledc ch%s gamma duty inc of current ram write address.This register is used to increase or decrease the duty of output signal on channel %s. 1: Increase 0: Decrease."]
    #[inline(always)]
    pub fn ch_gamma_duty_inc(&mut self) -> CH_GAMMA_DUTY_INC_W<'_, CH_GAMMA_WR_SPEC> {
        CH_GAMMA_DUTY_INC_W::new(self, 0)
    }
    #[doc = "Bits 1:10 - Ledc ch%s gamma duty cycle of current ram write address.The duty will change every LEDC_CH%s_GAMMA_DUTY_CYCLE on channel %s."]
    #[inline(always)]
    pub fn ch_gamma_duty_cycle(&mut self) -> CH_GAMMA_DUTY_CYCLE_W<'_, CH_GAMMA_WR_SPEC> {
        CH_GAMMA_DUTY_CYCLE_W::new(self, 1)
    }
    #[doc = "Bits 11:20 - Ledc ch%s gamma scale of current ram write address.This register is used to configure the changing step scale of duty on channel %s."]
    #[inline(always)]
    pub fn ch_gamma_scale(&mut self) -> CH_GAMMA_SCALE_W<'_, CH_GAMMA_WR_SPEC> {
        CH_GAMMA_SCALE_W::new(self, 11)
    }
    #[doc = "Bits 21:30 - Ledc ch%s gamma duty num of current ram write address.This register is used to control the number of times the duty cycle will be changed."]
    #[inline(always)]
    pub fn ch_gamma_duty_num(&mut self) -> CH_GAMMA_DUTY_NUM_W<'_, CH_GAMMA_WR_SPEC> {
        CH_GAMMA_DUTY_NUM_W::new(self, 21)
    }
}
#[doc = "Ledc ch%s gamma ram write register.\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_gamma_wr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_gamma_wr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CH_GAMMA_WR_SPEC;
impl crate::RegisterSpec for CH_GAMMA_WR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch_gamma_wr::R`](R) reader structure"]
impl crate::Readable for CH_GAMMA_WR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ch_gamma_wr::W`](W) writer structure"]
impl crate::Writable for CH_GAMMA_WR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CH%s_GAMMA_WR to value 0"]
impl crate::Resettable for CH_GAMMA_WR_SPEC {}
