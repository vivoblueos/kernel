#[doc = "Register `WORD1` reader"]
pub type R = crate::R<WORD1_SPEC>;
#[doc = "Register `WORD1` writer"]
pub type W = crate::W<WORD1_SPEC>;
#[doc = "Field `SEND_WORD` reader - a"]
pub type SEND_WORD_R = crate::FieldReader<u32>;
#[doc = "Field `SEND_WORD` writer - a"]
pub type SEND_WORD_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - a"]
    #[inline(always)]
    pub fn send_word(&self) -> SEND_WORD_R {
        SEND_WORD_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("WORD1")
            .field("send_word", &self.send_word())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - a"]
    #[inline(always)]
    pub fn send_word(&mut self) -> SEND_WORD_W<'_, WORD1_SPEC> {
        SEND_WORD_W::new(self, 0)
    }
}
#[doc = "a\n\nYou can [`read`](crate::Reg::read) this register and get [`word1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`word1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct WORD1_SPEC;
impl crate::RegisterSpec for WORD1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`word1::R`](R) reader structure"]
impl crate::Readable for WORD1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`word1::W`](W) writer structure"]
impl crate::Writable for WORD1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets WORD1 to value 0"]
impl crate::Resettable for WORD1_SPEC {}
