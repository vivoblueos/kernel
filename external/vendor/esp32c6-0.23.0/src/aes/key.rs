#[doc = "Register `KEY%s` reader"]
pub type R = crate::R<KEY_SPEC>;
#[doc = "Register `KEY%s` writer"]
pub type W = crate::W<KEY_SPEC>;
#[doc = "Field `KEY` reader - This bits stores key_0 that is a part of key material."]
pub type KEY_R = crate::FieldReader<u32>;
#[doc = "Field `KEY` writer - This bits stores key_0 that is a part of key material."]
pub type KEY_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32, crate::Safe>;
impl R {
    #[doc = "Bits 0:31 - This bits stores key_0 that is a part of key material."]
    #[inline(always)]
    pub fn key(&self) -> KEY_R {
        KEY_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("KEY").field("key", &self.key()).finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - This bits stores key_0 that is a part of key material."]
    #[inline(always)]
    pub fn key(&mut self) -> KEY_W<'_, KEY_SPEC> {
        KEY_W::new(self, 0)
    }
}
#[doc = "Key material key_%s configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`key::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`key::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct KEY_SPEC;
impl crate::RegisterSpec for KEY_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`key::R`](R) reader structure"]
impl crate::Readable for KEY_SPEC {}
#[doc = "`write(|w| ..)` method takes [`key::W`](W) writer structure"]
impl crate::Writable for KEY_SPEC {
    type Safety = crate::Safe;
}
#[doc = "`reset()` method sets KEY%s to value 0"]
impl crate::Resettable for KEY_SPEC {}
