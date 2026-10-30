#[doc = "Register `SCL_HIGH_PERIOD` reader"]
pub type R = crate::R<SCL_HIGH_PERIOD_SPEC>;
#[doc = "Register `SCL_HIGH_PERIOD` writer"]
pub type W = crate::W<SCL_HIGH_PERIOD_SPEC>;
#[doc = "Field `SCL_HIGH_PERIOD` reader - This register is used to configure for how long SCL remains high in master mode, in I2C module clock cycles."]
pub type SCL_HIGH_PERIOD_R = crate::FieldReader<u16>;
#[doc = "Field `SCL_HIGH_PERIOD` writer - This register is used to configure for how long SCL remains high in master mode, in I2C module clock cycles."]
pub type SCL_HIGH_PERIOD_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
#[doc = "Field `SCL_WAIT_HIGH_PERIOD` reader - This register is used to configure for the SCL_FSM's waiting period for SCL high level in master mode, in I2C module clock cycles."]
pub type SCL_WAIT_HIGH_PERIOD_R = crate::FieldReader;
#[doc = "Field `SCL_WAIT_HIGH_PERIOD` writer - This register is used to configure for the SCL_FSM's waiting period for SCL high level in master mode, in I2C module clock cycles."]
pub type SCL_WAIT_HIGH_PERIOD_W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
impl R {
    #[doc = "Bits 0:8 - This register is used to configure for how long SCL remains high in master mode, in I2C module clock cycles."]
    #[inline(always)]
    pub fn scl_high_period(&self) -> SCL_HIGH_PERIOD_R {
        SCL_HIGH_PERIOD_R::new((self.bits & 0x01ff) as u16)
    }
    #[doc = "Bits 9:15 - This register is used to configure for the SCL_FSM's waiting period for SCL high level in master mode, in I2C module clock cycles."]
    #[inline(always)]
    pub fn scl_wait_high_period(&self) -> SCL_WAIT_HIGH_PERIOD_R {
        SCL_WAIT_HIGH_PERIOD_R::new(((self.bits >> 9) & 0x7f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SCL_HIGH_PERIOD")
            .field("scl_high_period", &self.scl_high_period())
            .field("scl_wait_high_period", &self.scl_wait_high_period())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:8 - This register is used to configure for how long SCL remains high in master mode, in I2C module clock cycles."]
    #[inline(always)]
    pub fn scl_high_period(&mut self) -> SCL_HIGH_PERIOD_W<'_, SCL_HIGH_PERIOD_SPEC> {
        SCL_HIGH_PERIOD_W::new(self, 0)
    }
    #[doc = "Bits 9:15 - This register is used to configure for the SCL_FSM's waiting period for SCL high level in master mode, in I2C module clock cycles."]
    #[inline(always)]
    pub fn scl_wait_high_period(&mut self) -> SCL_WAIT_HIGH_PERIOD_W<'_, SCL_HIGH_PERIOD_SPEC> {
        SCL_WAIT_HIGH_PERIOD_W::new(self, 9)
    }
}
#[doc = "Configures the high level width of SCL\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_high_period::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_high_period::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SCL_HIGH_PERIOD_SPEC;
impl crate::RegisterSpec for SCL_HIGH_PERIOD_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`scl_high_period::R`](R) reader structure"]
impl crate::Readable for SCL_HIGH_PERIOD_SPEC {}
#[doc = "`write(|w| ..)` method takes [`scl_high_period::W`](W) writer structure"]
impl crate::Writable for SCL_HIGH_PERIOD_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SCL_HIGH_PERIOD to value 0"]
impl crate::Resettable for SCL_HIGH_PERIOD_SPEC {}
