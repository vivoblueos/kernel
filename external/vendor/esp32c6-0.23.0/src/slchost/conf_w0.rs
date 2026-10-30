#[doc = "Register `CONF_W0` reader"]
pub type R = crate::R<CONF_W0_SPEC>;
#[doc = "Register `CONF_W0` writer"]
pub type W = crate::W<CONF_W0_SPEC>;
#[doc = "Field `SLCHOST_CONF0` reader - *******Description***********"]
pub type SLCHOST_CONF0_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF0` writer - *******Description***********"]
pub type SLCHOST_CONF0_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF1` reader - *******Description***********"]
pub type SLCHOST_CONF1_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF1` writer - *******Description***********"]
pub type SLCHOST_CONF1_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF2` reader - *******Description***********"]
pub type SLCHOST_CONF2_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF2` writer - *******Description***********"]
pub type SLCHOST_CONF2_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SLCHOST_CONF3` reader - *******Description***********"]
pub type SLCHOST_CONF3_R = crate::FieldReader;
#[doc = "Field `SLCHOST_CONF3` writer - *******Description***********"]
pub type SLCHOST_CONF3_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf0(&self) -> SLCHOST_CONF0_R {
        SLCHOST_CONF0_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf1(&self) -> SLCHOST_CONF1_R {
        SLCHOST_CONF1_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf2(&self) -> SLCHOST_CONF2_R {
        SLCHOST_CONF2_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf3(&self) -> SLCHOST_CONF3_R {
        SLCHOST_CONF3_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF_W0")
            .field("slchost_conf0", &self.slchost_conf0())
            .field("slchost_conf1", &self.slchost_conf1())
            .field("slchost_conf2", &self.slchost_conf2())
            .field("slchost_conf3", &self.slchost_conf3())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf0(&mut self) -> SLCHOST_CONF0_W<'_, CONF_W0_SPEC> {
        SLCHOST_CONF0_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf1(&mut self) -> SLCHOST_CONF1_W<'_, CONF_W0_SPEC> {
        SLCHOST_CONF1_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf2(&mut self) -> SLCHOST_CONF2_W<'_, CONF_W0_SPEC> {
        SLCHOST_CONF2_W::new(self, 16)
    }
    #[doc = "Bits 24:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_conf3(&mut self) -> SLCHOST_CONF3_W<'_, CONF_W0_SPEC> {
        SLCHOST_CONF3_W::new(self, 24)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF_W0_SPEC;
impl crate::RegisterSpec for CONF_W0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf_w0::R`](R) reader structure"]
impl crate::Readable for CONF_W0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf_w0::W`](W) writer structure"]
impl crate::Writable for CONF_W0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF_W0 to value 0"]
impl crate::Resettable for CONF_W0_SPEC {}
