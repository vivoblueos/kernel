#[doc = "Register `CONF_W9` reader"]
pub type R = crate::R<CONF_W9_SPEC>;
#[doc = "Register `CONF_W9` writer"]
pub type W = crate::W<CONF_W9_SPEC>;
#[doc = "Field `SLCHOST_CONF36` reader - *******Description***********"]
pub type SLCHOST_CONF36_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF36` writer - *******Description***********"]
pub type SLCHOST_CONF36_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF37` reader - *******Description***********"]
pub type SLCHOST_CONF37_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF37` writer - *******Description***********"]
pub type SLCHOST_CONF37_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF38` reader - *******Description***********"]
pub type SLCHOST_CONF38_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF38` writer - *******Description***********"]
pub type SLCHOST_CONF38_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF39` reader - *******Description***********"]
pub type SLCHOST_CONF39_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF39` writer - *******Description***********"]
pub type SLCHOST_CONF39_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf36(&self) -> SLCHOST_CONF36_R {
        SLCHOST_CONF36_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf37(&self) -> SLCHOST_CONF37_R {
        SLCHOST_CONF37_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf38(&self) -> SLCHOST_CONF38_R {
        SLCHOST_CONF38_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf39(&self) -> SLCHOST_CONF39_R {
        SLCHOST_CONF39_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF_W9")
            .field("slchost_conf36", &self.slchost_conf36())
            .field("slchost_conf37", &self.slchost_conf37())
            .field("slchost_conf38", &self.slchost_conf38())
            .field("slchost_conf39", &self.slchost_conf39())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf36(&mut self) -> SLCHOST_CONF36_W<'_, CONF_W9_SPEC> {
        SLCHOST_CONF36_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf37(&mut self) -> SLCHOST_CONF37_W<'_, CONF_W9_SPEC> {
        SLCHOST_CONF37_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf38(&mut self) -> SLCHOST_CONF38_W<'_, CONF_W9_SPEC> {
        SLCHOST_CONF38_W::new(self, 16)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf39(&mut self) -> SLCHOST_CONF39_W<'_, CONF_W9_SPEC> {
        SLCHOST_CONF39_W::new(self, 24)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w9::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w9::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF_W9_SPEC;
impl crate::RegisterSpec for CONF_W9_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf_w9::R`](R) reader structure"]
impl crate::Readable for CONF_W9_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf_w9::W`](W) writer structure"]
impl crate::Writable for CONF_W9_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF_W9 to value 0"]
impl crate::Resettable for CONF_W9_SPEC {}
