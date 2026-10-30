#[doc = "Register `GEN_CTRL` reader"]
pub type R = crate::R<GEN_CTRL_SPEC>;
#[doc = "Register `GEN_CTRL` writer"]
pub type W = crate::W<GEN_CTRL_SPEC>;
#[doc = "Field `IQ_EST_FORCE_PD` reader - Force Power Down for IQ Estimation"]
pub type IQ_EST_FORCE_PD_R = crate::BitReader;
#[doc = "Field `IQ_EST_FORCE_PD` writer - Force Power Down for IQ Estimation"]
pub type IQ_EST_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IQ_EST_FORCE_PU` reader - Force Power Up for IQ Estimation"]
pub type IQ_EST_FORCE_PU_R = crate::BitReader;
#[doc = "Field `IQ_EST_FORCE_PU` writer - Force Power Up for IQ Estimation"]
pub type IQ_EST_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 4 - Force Power Down for IQ Estimation"]
    #[inline(always)]
    pub fn iq_est_force_pd(&self) -> IQ_EST_FORCE_PD_R {
        IQ_EST_FORCE_PD_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Force Power Up for IQ Estimation"]
    #[inline(always)]
    pub fn iq_est_force_pu(&self) -> IQ_EST_FORCE_PU_R {
        IQ_EST_FORCE_PU_R::new(((self.bits >> 5) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("GEN_CTRL")
            .field("iq_est_force_pu", &self.iq_est_force_pu())
            .field("iq_est_force_pd", &self.iq_est_force_pd())
            .finish()
    }
}
impl W {
    #[doc = "Bit 4 - Force Power Down for IQ Estimation"]
    #[inline(always)]
    pub fn iq_est_force_pd(&mut self) -> IQ_EST_FORCE_PD_W<'_, GEN_CTRL_SPEC> {
        IQ_EST_FORCE_PD_W::new(self, 4)
    }
    #[doc = "Bit 5 - Force Power Up for IQ Estimation"]
    #[inline(always)]
    pub fn iq_est_force_pu(&mut self) -> IQ_EST_FORCE_PU_W<'_, GEN_CTRL_SPEC> {
        IQ_EST_FORCE_PU_W::new(self, 5)
    }
}
#[doc = "FE General Control Register\n\nYou can [`read`](crate::Reg::read) this register and get [`gen_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`gen_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GEN_CTRL_SPEC;
impl crate::RegisterSpec for GEN_CTRL_SPEC {
    type Ux = u8;
}
#[doc = "`read()` method returns [`gen_ctrl::R`](R) reader structure"]
impl crate::Readable for GEN_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`gen_ctrl::W`](W) writer structure"]
impl crate::Writable for GEN_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets GEN_CTRL to value 0"]
impl crate::Resettable for GEN_CTRL_SPEC {}
