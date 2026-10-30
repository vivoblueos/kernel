#[doc = "Register `CH%s_GAMMA_WR_ADDR` reader"]
pub type R = crate::R<CH_GAMMA_WR_ADDR_SPEC>;
#[doc = "Register `CH%s_GAMMA_WR_ADDR` writer"]
pub type W = crate::W<CH_GAMMA_WR_ADDR_SPEC>;
#[doc = "Field `CH_GAMMA_WR_ADDR` reader - Ledc ch%s gamma ram write address."]
pub type CH_GAMMA_WR_ADDR_R = crate::FieldReader;
#[doc = "Field `CH_GAMMA_WR_ADDR` writer - Ledc ch%s gamma ram write address."]
pub type CH_GAMMA_WR_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3 - Ledc ch%s gamma ram write address."]
    #[inline(always)]
    pub fn ch_gamma_wr_addr(&self) -> CH_GAMMA_WR_ADDR_R {
        CH_GAMMA_WR_ADDR_R::new((self.bits & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CH_GAMMA_WR_ADDR")
            .field("ch_gamma_wr_addr", &self.ch_gamma_wr_addr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3 - Ledc ch%s gamma ram write address."]
    #[inline(always)]
    pub fn ch_gamma_wr_addr(&mut self) -> CH_GAMMA_WR_ADDR_W<'_, CH_GAMMA_WR_ADDR_SPEC> {
        CH_GAMMA_WR_ADDR_W::new(self, 0)
    }
}
#[doc = "Ledc ch%s gamma ram write address register.\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_gamma_wr_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_gamma_wr_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CH_GAMMA_WR_ADDR_SPEC;
impl crate::RegisterSpec for CH_GAMMA_WR_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch_gamma_wr_addr::R`](R) reader structure"]
impl crate::Readable for CH_GAMMA_WR_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ch_gamma_wr_addr::W`](W) writer structure"]
impl crate::Writable for CH_GAMMA_WR_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CH%s_GAMMA_WR_ADDR to value 0"]
impl crate::Resettable for CH_GAMMA_WR_ADDR_SPEC {}
