#[doc = "Register `DEVICE_EN` reader"]
pub type R = crate::R<DEVICE_EN_SPEC>;
#[doc = "Register `DEVICE_EN` writer"]
pub type W = crate::W<DEVICE_EN_SPEC>;
#[doc = "Field `LP_I2C_ANA_MAST_I2C_DEVICE_EN` reader - need_des"]
pub type LP_I2C_ANA_MAST_I2C_DEVICE_EN_R = crate::FieldReader<u16>;
#[doc = "Field `LP_I2C_ANA_MAST_I2C_DEVICE_EN` writer - need_des"]
pub type LP_I2C_ANA_MAST_I2C_DEVICE_EN_W<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
impl R {
    #[doc = "Bits 0:11 - need_des"]
    #[inline(always)]
    pub fn lp_i2c_ana_mast_i2c_device_en(&self) -> LP_I2C_ANA_MAST_I2C_DEVICE_EN_R {
        LP_I2C_ANA_MAST_I2C_DEVICE_EN_R::new((self.bits & 0x0fff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DEVICE_EN")
            .field(
                "lp_i2c_ana_mast_i2c_device_en",
                &self.lp_i2c_ana_mast_i2c_device_en(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:11 - need_des"]
    #[inline(always)]
    pub fn lp_i2c_ana_mast_i2c_device_en(
        &mut self,
    ) -> LP_I2C_ANA_MAST_I2C_DEVICE_EN_W<'_, DEVICE_EN_SPEC> {
        LP_I2C_ANA_MAST_I2C_DEVICE_EN_W::new(self, 0)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`device_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`device_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DEVICE_EN_SPEC;
impl crate::RegisterSpec for DEVICE_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`device_en::R`](R) reader structure"]
impl crate::Readable for DEVICE_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`device_en::W`](W) writer structure"]
impl crate::Writable for DEVICE_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DEVICE_EN to value 0"]
impl crate::Resettable for DEVICE_EN_SPEC {}
