#[doc = "Register `CONF_W6` reader"]
pub type R = crate::R<CONF_W6_SPEC>;
#[doc = "Register `CONF_W6` writer"]
pub type W = crate::W<CONF_W6_SPEC>;
#[doc = "Field `SLCHOST_CONF24` reader - *******Description***********"]
pub type SLCHOST_CONF24_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF24` writer - *******Description***********"]
pub type SLCHOST_CONF24_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF25` reader - *******Description***********"]
pub type SLCHOST_CONF25_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF25` writer - *******Description***********"]
pub type SLCHOST_CONF25_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF26` reader - *******Description***********"]
pub type SLCHOST_CONF26_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF26` writer - *******Description***********"]
pub type SLCHOST_CONF26_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF27` reader - *******Description***********"]
pub type SLCHOST_CONF27_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF27` writer - *******Description***********"]
pub type SLCHOST_CONF27_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf24(&self) -> SLCHOST_CONF24_R {
        SLCHOST_CONF24_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf25(&self) -> SLCHOST_CONF25_R {
        SLCHOST_CONF25_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf26(&self) -> SLCHOST_CONF26_R {
        SLCHOST_CONF26_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf27(&self) -> SLCHOST_CONF27_R {
        SLCHOST_CONF27_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF_W6")
            .field("slchost_conf24", &self.slchost_conf24())
            .field("slchost_conf25", &self.slchost_conf25())
            .field("slchost_conf26", &self.slchost_conf26())
            .field("slchost_conf27", &self.slchost_conf27())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf24(&mut self) -> SLCHOST_CONF24_W<'_, CONF_W6_SPEC> {
        SLCHOST_CONF24_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf25(&mut self) -> SLCHOST_CONF25_W<'_, CONF_W6_SPEC> {
        SLCHOST_CONF25_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf26(&mut self) -> SLCHOST_CONF26_W<'_, CONF_W6_SPEC> {
        SLCHOST_CONF26_W::new(self, 16)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf27(&mut self) -> SLCHOST_CONF27_W<'_, CONF_W6_SPEC> {
        SLCHOST_CONF27_W::new(self, 24)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w6::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w6::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF_W6_SPEC;
impl crate::RegisterSpec for CONF_W6_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf_w6::R`](R) reader structure"]
impl crate::Readable for CONF_W6_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf_w6::W`](W) writer structure"]
impl crate::Writable for CONF_W6_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF_W6 to value 0"]
impl crate::Resettable for CONF_W6_SPEC {}
