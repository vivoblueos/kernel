#[doc = "Register `SCL_STOP_HOLD` reader"]
pub type R = crate::R<SCL_STOP_HOLD_SPEC>;
#[doc = "Register `SCL_STOP_HOLD` writer"]
pub type W = crate::W<SCL_STOP_HOLD_SPEC>;
#[doc = "Field `TIME` reader - This register is used to configure the delay after the STOP condition, in I2C module clock cycles."]
pub type TIME_R = crate::FieldReader<u16>;
#[doc = "Field `TIME` writer - This register is used to configure the delay after the STOP condition, in I2C module clock cycles."]
pub type TIME_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
impl R {
    #[doc = "Bits 0:8 - This register is used to configure the delay after the STOP condition, in I2C module clock cycles."]
    #[inline(always)]
    pub fn time(&self) -> TIME_R {
        TIME_R::new((self.bits & 0x01ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SCL_STOP_HOLD")
            .field("time", &self.time())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:8 - This register is used to configure the delay after the STOP condition, in I2C module clock cycles."]
    #[inline(always)]
    pub fn time(&mut self) -> TIME_W<'_, SCL_STOP_HOLD_SPEC> {
        TIME_W::new(self, 0)
    }
}
#[doc = "Configures the delay after the SCL clock edge for a stop condition\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_stop_hold::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_stop_hold::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SCL_STOP_HOLD_SPEC;
impl crate::RegisterSpec for SCL_STOP_HOLD_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`scl_stop_hold::R`](R) reader structure"]
impl crate::Readable for SCL_STOP_HOLD_SPEC {}
#[doc = "`write(|w| ..)` method takes [`scl_stop_hold::W`](W) writer structure"]
impl crate::Writable for SCL_STOP_HOLD_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SCL_STOP_HOLD to value 0x08"]
impl crate::Resettable for SCL_STOP_HOLD_SPEC {
    const RESET_VALUE: u32 = 0x08;
}
