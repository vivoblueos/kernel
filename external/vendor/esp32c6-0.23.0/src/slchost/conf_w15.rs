#[doc = "Register `CONF_W15` reader"]
pub type R = crate::R<CONF_W15_SPEC>;
#[doc = "Register `CONF_W15` writer"]
pub type W = crate::W<CONF_W15_SPEC>;
#[doc = "Field `SLCHOST_CONF60` reader - *******Description***********"]
pub type SLCHOST_CONF60_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF60` writer - *******Description***********"]
pub type SLCHOST_CONF60_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF61` reader - *******Description***********"]
pub type SLCHOST_CONF61_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF61` writer - *******Description***********"]
pub type SLCHOST_CONF61_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF62` reader - *******Description***********"]
pub type SLCHOST_CONF62_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF62` writer - *******Description***********"]
pub type SLCHOST_CONF62_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF63` reader - *******Description***********"]
pub type SLCHOST_CONF63_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF63` writer - *******Description***********"]
pub type SLCHOST_CONF63_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf60(&self) -> SLCHOST_CONF60_R {
        SLCHOST_CONF60_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf61(&self) -> SLCHOST_CONF61_R {
        SLCHOST_CONF61_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf62(&self) -> SLCHOST_CONF62_R {
        SLCHOST_CONF62_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf63(&self) -> SLCHOST_CONF63_R {
        SLCHOST_CONF63_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF_W15")
            .field("slchost_conf60", &self.slchost_conf60())
            .field("slchost_conf61", &self.slchost_conf61())
            .field("slchost_conf62", &self.slchost_conf62())
            .field("slchost_conf63", &self.slchost_conf63())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf60(&mut self) -> SLCHOST_CONF60_W<'_, CONF_W15_SPEC> {
        SLCHOST_CONF60_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf61(&mut self) -> SLCHOST_CONF61_W<'_, CONF_W15_SPEC> {
        SLCHOST_CONF61_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf62(&mut self) -> SLCHOST_CONF62_W<'_, CONF_W15_SPEC> {
        SLCHOST_CONF62_W::new(self, 16)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf63(&mut self) -> SLCHOST_CONF63_W<'_, CONF_W15_SPEC> {
        SLCHOST_CONF63_W::new(self, 24)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w15::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w15::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF_W15_SPEC;
impl crate::RegisterSpec for CONF_W15_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf_w15::R`](R) reader structure"]
impl crate::Readable for CONF_W15_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf_w15::W`](W) writer structure"]
impl crate::Writable for CONF_W15_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF_W15 to value 0"]
impl crate::Resettable for CONF_W15_SPEC {}
