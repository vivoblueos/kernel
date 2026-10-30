#[doc = "Register `CONF_W11` reader"]
pub type R = crate::R<CONF_W11_SPEC>;
#[doc = "Register `CONF_W11` writer"]
pub type W = crate::W<CONF_W11_SPEC>;
#[doc = "Field `SLCHOST_CONF44` reader - *******Description***********"]
pub type SLCHOST_CONF44_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF44` writer - *******Description***********"]
pub type SLCHOST_CONF44_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF45` reader - *******Description***********"]
pub type SLCHOST_CONF45_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF45` writer - *******Description***********"]
pub type SLCHOST_CONF45_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF46` reader - *******Description***********"]
pub type SLCHOST_CONF46_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF46` writer - *******Description***********"]
pub type SLCHOST_CONF46_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF47` reader - *******Description***********"]
pub type SLCHOST_CONF47_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF47` writer - *******Description***********"]
pub type SLCHOST_CONF47_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf44(&self) -> SLCHOST_CONF44_R {
        SLCHOST_CONF44_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf45(&self) -> SLCHOST_CONF45_R {
        SLCHOST_CONF45_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf46(&self) -> SLCHOST_CONF46_R {
        SLCHOST_CONF46_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf47(&self) -> SLCHOST_CONF47_R {
        SLCHOST_CONF47_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF_W11")
            .field("slchost_conf44", &self.slchost_conf44())
            .field("slchost_conf45", &self.slchost_conf45())
            .field("slchost_conf46", &self.slchost_conf46())
            .field("slchost_conf47", &self.slchost_conf47())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf44(&mut self) -> SLCHOST_CONF44_W<'_, CONF_W11_SPEC> {
        SLCHOST_CONF44_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf45(&mut self) -> SLCHOST_CONF45_W<'_, CONF_W11_SPEC> {
        SLCHOST_CONF45_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf46(&mut self) -> SLCHOST_CONF46_W<'_, CONF_W11_SPEC> {
        SLCHOST_CONF46_W::new(self, 16)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf47(&mut self) -> SLCHOST_CONF47_W<'_, CONF_W11_SPEC> {
        SLCHOST_CONF47_W::new(self, 24)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w11::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w11::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF_W11_SPEC;
impl crate::RegisterSpec for CONF_W11_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf_w11::R`](R) reader structure"]
impl crate::Readable for CONF_W11_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf_w11::W`](W) writer structure"]
impl crate::Writable for CONF_W11_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF_W11 to value 0"]
impl crate::Resettable for CONF_W11_SPEC {}
