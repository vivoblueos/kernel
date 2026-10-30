#[doc = "Register `SDA_HOLD` reader"]
pub type R = crate::R<SDA_HOLD_SPEC>;
#[doc = "Register `SDA_HOLD` writer"]
pub type W = crate::W<SDA_HOLD_SPEC>;
#[doc = "Field `TIME` reader - reg_sda_hold_time"]
pub type TIME_R = crate::FieldReader<u16>;
#[doc = "Field `TIME` writer - reg_sda_hold_time"]
pub type TIME_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
impl R {
    #[doc = "Bits 0:8 - reg_sda_hold_time"]
    #[inline(always)]
    pub fn time(&self) -> TIME_R {
        TIME_R::new((self.bits & 0x01ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SDA_HOLD")
            .field("time", &self.time())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:8 - reg_sda_hold_time"]
    #[inline(always)]
    pub fn time(&mut self) -> TIME_W<'_, SDA_HOLD_SPEC> {
        TIME_W::new(self, 0)
    }
}
#[doc = "I2C_SDA_HOLD_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`sda_hold::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sda_hold::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SDA_HOLD_SPEC;
impl crate::RegisterSpec for SDA_HOLD_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sda_hold::R`](R) reader structure"]
impl crate::Readable for SDA_HOLD_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sda_hold::W`](W) writer structure"]
impl crate::Writable for SDA_HOLD_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SDA_HOLD to value 0"]
impl crate::Resettable for SDA_HOLD_SPEC {}
