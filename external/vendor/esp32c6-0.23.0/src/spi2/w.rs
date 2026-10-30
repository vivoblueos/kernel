#[doc = "Register `W%s` reader"]
pub type R = crate::R<W_SPEC>;
#[doc = "Register `W%s` writer"]
pub type W = crate::W<W_SPEC>;
#[doc = "Field `BUF` reader - data buffer"]
pub type BUF_R = crate::FieldReader<u32>;
#[doc = "Field `BUF` writer - data buffer"]
pub type BUF_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32, crate::Safe>;
impl R {
    #[doc = "Bits 0:31 - data buffer"]
    #[inline(always)]
    pub fn buf(&self) -> BUF_R {
        BUF_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("W").field("buf", &self.buf()).finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - data buffer"]
    #[inline(always)]
    pub fn buf(&mut self) -> BUF_W<'_, W_SPEC> {
        BUF_W::new(self, 0)
    }
}
#[doc = "SPI CPU-controlled buffer%s\n\nYou can [`read`](crate::Reg::read) this register and get [`w::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`w::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct W_SPEC;
impl crate::RegisterSpec for W_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`w::R`](R) reader structure"]
impl crate::Readable for W_SPEC {}
#[doc = "`write(|w| ..)` method takes [`w::W`](W) writer structure"]
impl crate::Writable for W_SPEC {
    type Safety = crate::Safe;
}
#[doc = "`reset()` method sets W%s to value 0"]
impl crate::Resettable for W_SPEC {}
