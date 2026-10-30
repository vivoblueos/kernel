#[doc = "Register `CONF_W3` reader"]
pub type R = crate::R<CONF_W3_SPEC>;
#[doc = "Register `CONF_W3` writer"]
pub type W = crate::W<CONF_W3_SPEC>;
#[doc = "Field `SLCHOST_CONF12` reader - *******Description***********"]
pub type SLCHOST_CONF12_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF12` writer - *******Description***********"]
pub type SLCHOST_CONF12_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF13` reader - *******Description***********"]
pub type SLCHOST_CONF13_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF13` writer - *******Description***********"]
pub type SLCHOST_CONF13_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF14` reader - *******Description***********"]
pub type SLCHOST_CONF14_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF14` writer - *******Description***********"]
pub type SLCHOST_CONF14_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF15` reader - *******Description***********"]
pub type SLCHOST_CONF15_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF15` writer - *******Description***********"]
pub type SLCHOST_CONF15_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf12(&self) -> SLCHOST_CONF12_R {
        SLCHOST_CONF12_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf13(&self) -> SLCHOST_CONF13_R {
        SLCHOST_CONF13_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf14(&self) -> SLCHOST_CONF14_R {
        SLCHOST_CONF14_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf15(&self) -> SLCHOST_CONF15_R {
        SLCHOST_CONF15_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF_W3")
            .field("slchost_conf12", &self.slchost_conf12())
            .field("slchost_conf13", &self.slchost_conf13())
            .field("slchost_conf14", &self.slchost_conf14())
            .field("slchost_conf15", &self.slchost_conf15())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf12(&mut self) -> SLCHOST_CONF12_W<'_, CONF_W3_SPEC> {
        SLCHOST_CONF12_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf13(&mut self) -> SLCHOST_CONF13_W<'_, CONF_W3_SPEC> {
        SLCHOST_CONF13_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf14(&mut self) -> SLCHOST_CONF14_W<'_, CONF_W3_SPEC> {
        SLCHOST_CONF14_W::new(self, 16)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf15(&mut self) -> SLCHOST_CONF15_W<'_, CONF_W3_SPEC> {
        SLCHOST_CONF15_W::new(self, 24)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w3::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w3::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF_W3_SPEC;
impl crate::RegisterSpec for CONF_W3_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf_w3::R`](R) reader structure"]
impl crate::Readable for CONF_W3_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf_w3::W`](W) writer structure"]
impl crate::Writable for CONF_W3_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF_W3 to value 0xc0"]
impl crate::Resettable for CONF_W3_SPEC {
    const RESET_VALUE: u32 = 0xc0;
}
