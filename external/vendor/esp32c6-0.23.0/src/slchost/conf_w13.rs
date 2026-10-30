#[doc = "Register `CONF_W13` reader"]
pub type R = crate::R<CONF_W13_SPEC>;
#[doc = "Register `CONF_W13` writer"]
pub type W = crate::W<CONF_W13_SPEC>;
#[doc = "Field `SLCHOST_CONF52` reader - *******Description***********"]
pub type SLCHOST_CONF52_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF52` writer - *******Description***********"]
pub type SLCHOST_CONF52_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF53` reader - *******Description***********"]
pub type SLCHOST_CONF53_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF53` writer - *******Description***********"]
pub type SLCHOST_CONF53_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF54` reader - *******Description***********"]
pub type SLCHOST_CONF54_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF54` writer - *******Description***********"]
pub type SLCHOST_CONF54_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF55` reader - *******Description***********"]
pub type SLCHOST_CONF55_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF55` writer - *******Description***********"]
pub type SLCHOST_CONF55_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf52(&self) -> SLCHOST_CONF52_R {
        SLCHOST_CONF52_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf53(&self) -> SLCHOST_CONF53_R {
        SLCHOST_CONF53_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf54(&self) -> SLCHOST_CONF54_R {
        SLCHOST_CONF54_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf55(&self) -> SLCHOST_CONF55_R {
        SLCHOST_CONF55_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF_W13")
            .field("slchost_conf52", &self.slchost_conf52())
            .field("slchost_conf53", &self.slchost_conf53())
            .field("slchost_conf54", &self.slchost_conf54())
            .field("slchost_conf55", &self.slchost_conf55())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf52(&mut self) -> SLCHOST_CONF52_W<'_, CONF_W13_SPEC> {
        SLCHOST_CONF52_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf53(&mut self) -> SLCHOST_CONF53_W<'_, CONF_W13_SPEC> {
        SLCHOST_CONF53_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf54(&mut self) -> SLCHOST_CONF54_W<'_, CONF_W13_SPEC> {
        SLCHOST_CONF54_W::new(self, 16)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf55(&mut self) -> SLCHOST_CONF55_W<'_, CONF_W13_SPEC> {
        SLCHOST_CONF55_W::new(self, 24)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w13::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w13::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF_W13_SPEC;
impl crate::RegisterSpec for CONF_W13_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf_w13::R`](R) reader structure"]
impl crate::Readable for CONF_W13_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf_w13::W`](W) writer structure"]
impl crate::Writable for CONF_W13_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF_W13 to value 0"]
impl crate::Resettable for CONF_W13_SPEC {}
