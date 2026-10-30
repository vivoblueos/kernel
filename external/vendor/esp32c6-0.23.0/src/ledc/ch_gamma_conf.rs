#[doc = "Register `CH%s_GAMMA_CONF` reader"]
pub type R = crate::R<CH_GAMMA_CONF_SPEC>;
#[doc = "Register `CH%s_GAMMA_CONF` writer"]
pub type W = crate::W<CH_GAMMA_CONF_SPEC>;
#[doc = "Field `CH_GAMMA_ENTRY_NUM` reader - Ledc ch%s gamma entry num."]
pub type CH_GAMMA_ENTRY_NUM_R = crate::FieldReader;
#[doc = "Field `CH_GAMMA_ENTRY_NUM` writer - Ledc ch%s gamma entry num."]
pub type CH_GAMMA_ENTRY_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `CH_GAMMA_PAUSE` writer - Ledc ch%s gamma pause, write 1 to pause."]
pub type CH_GAMMA_PAUSE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH_GAMMA_RESUME` writer - Ledc ch%s gamma resume, write 1 to resume."]
pub type CH_GAMMA_RESUME_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:4 - Ledc ch%s gamma entry num."]
    #[inline(always)]
    pub fn ch_gamma_entry_num(&self) -> CH_GAMMA_ENTRY_NUM_R {
        CH_GAMMA_ENTRY_NUM_R::new((self.bits & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CH_GAMMA_CONF")
            .field("ch_gamma_entry_num", &self.ch_gamma_entry_num())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:4 - Ledc ch%s gamma entry num."]
    #[inline(always)]
    pub fn ch_gamma_entry_num(&mut self) -> CH_GAMMA_ENTRY_NUM_W<'_, CH_GAMMA_CONF_SPEC> {
        CH_GAMMA_ENTRY_NUM_W::new(self, 0)
    }
    #[doc = "Bit 5 - Ledc ch%s gamma pause, write 1 to pause."]
    #[inline(always)]
    pub fn ch_gamma_pause(&mut self) -> CH_GAMMA_PAUSE_W<'_, CH_GAMMA_CONF_SPEC> {
        CH_GAMMA_PAUSE_W::new(self, 5)
    }
    #[doc = "Bit 6 - Ledc ch%s gamma resume, write 1 to resume."]
    #[inline(always)]
    pub fn ch_gamma_resume(&mut self) -> CH_GAMMA_RESUME_W<'_, CH_GAMMA_CONF_SPEC> {
        CH_GAMMA_RESUME_W::new(self, 6)
    }
}
#[doc = "Ledc ch%s gamma config register.\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_gamma_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_gamma_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CH_GAMMA_CONF_SPEC;
impl crate::RegisterSpec for CH_GAMMA_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch_gamma_conf::R`](R) reader structure"]
impl crate::Readable for CH_GAMMA_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ch_gamma_conf::W`](W) writer structure"]
impl crate::Writable for CH_GAMMA_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CH%s_GAMMA_CONF to value 0"]
impl crate::Resettable for CH_GAMMA_CONF_SPEC {}
