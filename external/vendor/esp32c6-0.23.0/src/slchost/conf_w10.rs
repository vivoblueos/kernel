#[doc = "Register `CONF_W10` reader"]
pub type R = crate::R<CONF_W10_SPEC>;
#[doc = "Register `CONF_W10` writer"]
pub type W = crate::W<CONF_W10_SPEC>;
#[doc = "Field `SLCHOST_CONF40` reader - *******Description***********"]
pub type SLCHOST_CONF40_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF40` writer - *******Description***********"]
pub type SLCHOST_CONF40_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF41` reader - *******Description***********"]
pub type SLCHOST_CONF41_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF41` writer - *******Description***********"]
pub type SLCHOST_CONF41_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF42` reader - *******Description***********"]
pub type SLCHOST_CONF42_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF42` writer - *******Description***********"]
pub type SLCHOST_CONF42_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF43` reader - *******Description***********"]
pub type SLCHOST_CONF43_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF43` writer - *******Description***********"]
pub type SLCHOST_CONF43_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf40(&self) -> SLCHOST_CONF40_R {
        SLCHOST_CONF40_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf41(&self) -> SLCHOST_CONF41_R {
        SLCHOST_CONF41_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf42(&self) -> SLCHOST_CONF42_R {
        SLCHOST_CONF42_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf43(&self) -> SLCHOST_CONF43_R {
        SLCHOST_CONF43_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF_W10")
            .field("slchost_conf40", &self.slchost_conf40())
            .field("slchost_conf41", &self.slchost_conf41())
            .field("slchost_conf42", &self.slchost_conf42())
            .field("slchost_conf43", &self.slchost_conf43())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf40(&mut self) -> SLCHOST_CONF40_W<'_, CONF_W10_SPEC> {
        SLCHOST_CONF40_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf41(&mut self) -> SLCHOST_CONF41_W<'_, CONF_W10_SPEC> {
        SLCHOST_CONF41_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf42(&mut self) -> SLCHOST_CONF42_W<'_, CONF_W10_SPEC> {
        SLCHOST_CONF42_W::new(self, 16)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf43(&mut self) -> SLCHOST_CONF43_W<'_, CONF_W10_SPEC> {
        SLCHOST_CONF43_W::new(self, 24)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w10::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w10::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF_W10_SPEC;
impl crate::RegisterSpec for CONF_W10_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf_w10::R`](R) reader structure"]
impl crate::Readable for CONF_W10_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf_w10::W`](W) writer structure"]
impl crate::Writable for CONF_W10_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF_W10 to value 0"]
impl crate::Resettable for CONF_W10_SPEC {}
