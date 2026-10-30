#[doc = "Register `CONF_W1` reader"]
pub type R = crate::R<CONF_W1_SPEC>;
#[doc = "Register `CONF_W1` writer"]
pub type W = crate::W<CONF_W1_SPEC>;
#[doc = "Field `SLCHOST_CONF4` reader - *******Description***********"]
pub type SLCHOST_CONF4_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF4` writer - *******Description***********"]
pub type SLCHOST_CONF4_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF5` reader - *******Description***********"]
pub type SLCHOST_CONF5_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF5` writer - *******Description***********"]
pub type SLCHOST_CONF5_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF6` reader - *******Description***********"]
pub type SLCHOST_CONF6_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF6` writer - *******Description***********"]
pub type SLCHOST_CONF6_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF7` reader - *******Description***********"]
pub type SLCHOST_CONF7_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF7` writer - *******Description***********"]
pub type SLCHOST_CONF7_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf4(&self) -> SLCHOST_CONF4_R {
        SLCHOST_CONF4_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf5(&self) -> SLCHOST_CONF5_R {
        SLCHOST_CONF5_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf6(&self) -> SLCHOST_CONF6_R {
        SLCHOST_CONF6_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf7(&self) -> SLCHOST_CONF7_R {
        SLCHOST_CONF7_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF_W1")
            .field("slchost_conf4", &self.slchost_conf4())
            .field("slchost_conf5", &self.slchost_conf5())
            .field("slchost_conf6", &self.slchost_conf6())
            .field("slchost_conf7", &self.slchost_conf7())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf4(&mut self) -> SLCHOST_CONF4_W<'_, CONF_W1_SPEC> {
        SLCHOST_CONF4_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf5(&mut self) -> SLCHOST_CONF5_W<'_, CONF_W1_SPEC> {
        SLCHOST_CONF5_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf6(&mut self) -> SLCHOST_CONF6_W<'_, CONF_W1_SPEC> {
        SLCHOST_CONF6_W::new(self, 16)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf7(&mut self) -> SLCHOST_CONF7_W<'_, CONF_W1_SPEC> {
        SLCHOST_CONF7_W::new(self, 24)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF_W1_SPEC;
impl crate::RegisterSpec for CONF_W1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf_w1::R`](R) reader structure"]
impl crate::Readable for CONF_W1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf_w1::W`](W) writer structure"]
impl crate::Writable for CONF_W1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF_W1 to value 0"]
impl crate::Resettable for CONF_W1_SPEC {}
