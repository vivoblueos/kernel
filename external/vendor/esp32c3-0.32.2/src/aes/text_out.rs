#[doc = "Register `TEXT_OUT%s` reader"]
pub type R = crate::R<TEXT_OUT_SPEC>;
#[doc = "Register `TEXT_OUT%s` writer"]
pub type W = crate::W<TEXT_OUT_SPEC>;
#[doc = "Field `TEXT_OUT` reader - This bits stores text_out_0 that is a part of result text material."]
pub type TEXT_OUT_R = crate::FieldReader<u32>;
#[doc = "Field `TEXT_OUT` writer - This bits stores text_out_0 that is a part of result text material."]
pub type TEXT_OUT_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - This bits stores text_out_0 that is a part of result text material."]
    #[inline(always)]
    pub fn text_out(&self) -> TEXT_OUT_R {
        TEXT_OUT_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TEXT_OUT")
            .field("text_out", &self.text_out())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - This bits stores text_out_0 that is a part of result text material."]
    #[inline(always)]
    pub fn text_out(&mut self) -> TEXT_OUT_W<'_, TEXT_OUT_SPEC> {
        TEXT_OUT_W::new(self, 0)
    }
}
#[doc = "result text material text_out_%s configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`text_out::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`text_out::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TEXT_OUT_SPEC;
impl crate::RegisterSpec for TEXT_OUT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`text_out::R`](R) reader structure"]
impl crate::Readable for TEXT_OUT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`text_out::W`](W) writer structure"]
impl crate::Writable for TEXT_OUT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TEXT_OUT%s to value 0"]
impl crate::Resettable for TEXT_OUT_SPEC {}
