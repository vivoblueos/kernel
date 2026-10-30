#[doc = "Register `TX_INTERP_CTRL` reader"]
pub type R = crate::R<TX_INTERP_CTRL_SPEC>;
#[doc = "Register `TX_INTERP_CTRL` writer"]
pub type W = crate::W<TX_INTERP_CTRL_SPEC>;
#[doc = "Field `TX_INF_FORCE_PD` reader - Force Power Down field"]
pub type TX_INF_FORCE_PD_R = crate::BitReader;
#[doc = "Field `TX_INF_FORCE_PD` writer - Force Power Down field"]
pub type TX_INF_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_INF_FORCE_PU` reader - Force Power Up field"]
pub type TX_INF_FORCE_PU_R = crate::BitReader;
#[doc = "Field `TX_INF_FORCE_PU` writer - Force Power Up field"]
pub type TX_INF_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 9 - Force Power Down field"]
    #[inline(always)]
    pub fn tx_inf_force_pd(&self) -> TX_INF_FORCE_PD_R {
        TX_INF_FORCE_PD_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Force Power Up field"]
    #[inline(always)]
    pub fn tx_inf_force_pu(&self) -> TX_INF_FORCE_PU_R {
        TX_INF_FORCE_PU_R::new(((self.bits >> 10) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_INTERP_CTRL")
            .field("tx_inf_force_pu", &self.tx_inf_force_pu())
            .field("tx_inf_force_pd", &self.tx_inf_force_pd())
            .finish()
    }
}
impl W {
    #[doc = "Bit 9 - Force Power Down field"]
    #[inline(always)]
    pub fn tx_inf_force_pd(&mut self) -> TX_INF_FORCE_PD_W<'_, TX_INTERP_CTRL_SPEC> {
        TX_INF_FORCE_PD_W::new(self, 9)
    }
    #[doc = "Bit 10 - Force Power Up field"]
    #[inline(always)]
    pub fn tx_inf_force_pu(&mut self) -> TX_INF_FORCE_PU_W<'_, TX_INTERP_CTRL_SPEC> {
        TX_INF_FORCE_PU_W::new(self, 10)
    }
}
#[doc = "FE2 TX Interpolation Control Register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_interp_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_interp_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_INTERP_CTRL_SPEC;
impl crate::RegisterSpec for TX_INTERP_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_interp_ctrl::R`](R) reader structure"]
impl crate::Readable for TX_INTERP_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_interp_ctrl::W`](W) writer structure"]
impl crate::Writable for TX_INTERP_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_INTERP_CTRL to value 0"]
impl crate::Resettable for TX_INTERP_CTRL_SPEC {}
