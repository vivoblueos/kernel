#[doc = "Register `SCL_LOW_PERIOD` reader"]
pub type R = crate::R<SCL_LOW_PERIOD_SPEC>;
#[doc = "Register `SCL_LOW_PERIOD` writer"]
pub type W = crate::W<SCL_LOW_PERIOD_SPEC>;
#[doc = "Field `SCL_LOW_PERIOD` reader - reg_scl_low_period"]
pub type SCL_LOW_PERIOD_R = crate::FieldReader<u16>;
#[doc = "Field `SCL_LOW_PERIOD` writer - reg_scl_low_period"]
pub type SCL_LOW_PERIOD_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
impl R {
    #[doc = "Bits 0:8 - reg_scl_low_period"]
    #[inline(always)]
    pub fn scl_low_period(&self) -> SCL_LOW_PERIOD_R {
        SCL_LOW_PERIOD_R::new((self.bits & 0x01ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SCL_LOW_PERIOD")
            .field("scl_low_period", &self.scl_low_period())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:8 - reg_scl_low_period"]
    #[inline(always)]
    pub fn scl_low_period(&mut self) -> SCL_LOW_PERIOD_W<'_, SCL_LOW_PERIOD_SPEC> {
        SCL_LOW_PERIOD_W::new(self, 0)
    }
}
#[doc = "I2C_SCL_LOW_PERIOD_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_low_period::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_low_period::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SCL_LOW_PERIOD_SPEC;
impl crate::RegisterSpec for SCL_LOW_PERIOD_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`scl_low_period::R`](R) reader structure"]
impl crate::Readable for SCL_LOW_PERIOD_SPEC {}
#[doc = "`write(|w| ..)` method takes [`scl_low_period::W`](W) writer structure"]
impl crate::Writable for SCL_LOW_PERIOD_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SCL_LOW_PERIOD to value 0"]
impl crate::Resettable for SCL_LOW_PERIOD_SPEC {}
