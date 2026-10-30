#[doc = "Register `TEXT_IN%s` reader"]
pub type R = crate::R<TEXT_IN_SPEC>;
#[doc = "Register `TEXT_IN%s` writer"]
pub type W = crate::W<TEXT_IN_SPEC>;
#[doc = "Field `TEXT_IN` reader - This bits stores text_in_0 that is a part of source text material."]
pub type TEXT_IN_R = crate::FieldReader<u32>;
#[doc = "Field `TEXT_IN` writer - This bits stores text_in_0 that is a part of source text material."]
pub type TEXT_IN_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32, crate::Safe>;
impl R {
    #[doc = "Bits 0:31 - This bits stores text_in_0 that is a part of source text material."]
    #[inline(always)]
    pub fn text_in(&self) -> TEXT_IN_R {
        TEXT_IN_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TEXT_IN")
            .field("text_in", &self.text_in())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - This bits stores text_in_0 that is a part of source text material."]
    #[inline(always)]
    pub fn text_in(&mut self) -> TEXT_IN_W<'_, TEXT_IN_SPEC> {
        TEXT_IN_W::new(self, 0)
    }
}
#[doc = "source text material text_in_%s configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`text_in::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`text_in::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TEXT_IN_SPEC;
impl crate::RegisterSpec for TEXT_IN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`text_in::R`](R) reader structure"]
impl crate::Readable for TEXT_IN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`text_in::W`](W) writer structure"]
impl crate::Writable for TEXT_IN_SPEC {
    type Safety = crate::Safe;
}
#[doc = "`reset()` method sets TEXT_IN%s to value 0"]
impl crate::Resettable for TEXT_IN_SPEC {}
