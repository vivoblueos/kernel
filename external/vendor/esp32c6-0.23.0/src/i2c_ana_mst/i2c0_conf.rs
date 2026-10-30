#[doc = "Register `I2C0_CONF` reader"]
pub type R = crate::R<I2C0_CONF_SPEC>;
#[doc = "Register `I2C0_CONF` writer"]
pub type W = crate::W<I2C0_CONF_SPEC>;
#[doc = "Field `CONF` reader - ?"]
pub type CONF_R = crate::FieldReader<u32>;
#[doc = "Field `CONF` writer - ?"]
pub type CONF_W<'a, REG> = crate::FieldWriter<'a, REG, 24, u32>;
#[doc = "Field `STATUS` reader - ?"]
pub type STATUS_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:23 - ?"]
    #[inline(always)]
    pub fn conf(&self) -> CONF_R {
        CONF_R::new(self.bits & 0x00ff_ffff)
    }
    #[doc = "Bits 24:31 - ?"]
    #[inline(always)]
    pub fn status(&self) -> STATUS_R {
        STATUS_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("I2C0_CONF")
            .field("conf", &self.conf())
            .field("status", &self.status())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:23 - ?"]
    #[inline(always)]
    pub fn conf(&mut self) -> CONF_W<'_, I2C0_CONF_SPEC> {
        CONF_W::new(self, 0)
    }
}
#[doc = "I2C0_CONF register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c0_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c0_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct I2C0_CONF_SPEC;
impl crate::RegisterSpec for I2C0_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`i2c0_conf::R`](R) reader structure"]
impl crate::Readable for I2C0_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`i2c0_conf::W`](W) writer structure"]
impl crate::Writable for I2C0_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets I2C0_CONF to value 0"]
impl crate::Resettable for I2C0_CONF_SPEC {}
