#[doc = "Register `ANA_CONF1` reader"]
pub type R = crate::R<ANA_CONF1_SPEC>;
#[doc = "Register `ANA_CONF1` writer"]
pub type W = crate::W<ANA_CONF1_SPEC>;
#[doc = "Field `LP_I2C_ANA_MAST_ANA_CONF1` reader - need_des"]
pub type LP_I2C_ANA_MAST_ANA_CONF1_R = crate::FieldReader<u32>;
#[doc = "Field `LP_I2C_ANA_MAST_ANA_CONF1` writer - need_des"]
pub type LP_I2C_ANA_MAST_ANA_CONF1_W<'a, REG> = crate::FieldWriter<'a, REG, 24, u32>;
impl R {
    #[doc = "Bits 0:23 - need_des"]
    #[inline(always)]
    pub fn lp_i2c_ana_mast_ana_conf1(&self) -> LP_I2C_ANA_MAST_ANA_CONF1_R {
        LP_I2C_ANA_MAST_ANA_CONF1_R::new(self.bits & 0x00ff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ANA_CONF1")
            .field(
                "lp_i2c_ana_mast_ana_conf1",
                &self.lp_i2c_ana_mast_ana_conf1(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:23 - need_des"]
    #[inline(always)]
    pub fn lp_i2c_ana_mast_ana_conf1(&mut self) -> LP_I2C_ANA_MAST_ANA_CONF1_W<'_, ANA_CONF1_SPEC> {
        LP_I2C_ANA_MAST_ANA_CONF1_W::new(self, 0)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`ana_conf1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ana_conf1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ANA_CONF1_SPEC;
impl crate::RegisterSpec for ANA_CONF1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ana_conf1::R`](R) reader structure"]
impl crate::Readable for ANA_CONF1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ana_conf1::W`](W) writer structure"]
impl crate::Writable for ANA_CONF1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ANA_CONF1 to value 0"]
impl crate::Resettable for ANA_CONF1_SPEC {}
