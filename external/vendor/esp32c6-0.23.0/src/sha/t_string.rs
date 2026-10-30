#[doc = "Register `T_STRING` reader"]
pub type R = crate::R<T_STRING_SPEC>;
#[doc = "Register `T_STRING` writer"]
pub type W = crate::W<T_STRING_SPEC>;
#[doc = "Field `T_STRING` reader - Sha t_string (used if and only if mode == SHA_512/t)."]
pub type T_STRING_R = crate::FieldReader<u32>;
#[doc = "Field `T_STRING` writer - Sha t_string (used if and only if mode == SHA_512/t)."]
pub type T_STRING_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Sha t_string (used if and only if mode == SHA_512/t)."]
    #[inline(always)]
    pub fn t_string(&self) -> T_STRING_R {
        T_STRING_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("T_STRING")
            .field("t_string", &self.t_string())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Sha t_string (used if and only if mode == SHA_512/t)."]
    #[inline(always)]
    pub fn t_string(&mut self) -> T_STRING_W<'_, T_STRING_SPEC> {
        T_STRING_W::new(self, 0)
    }
}
#[doc = "SHA 512/t configuration register 0.\n\nYou can [`read`](crate::Reg::read) this register and get [`t_string::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`t_string::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct T_STRING_SPEC;
impl crate::RegisterSpec for T_STRING_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`t_string::R`](R) reader structure"]
impl crate::Readable for T_STRING_SPEC {}
#[doc = "`write(|w| ..)` method takes [`t_string::W`](W) writer structure"]
impl crate::Writable for T_STRING_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets T_STRING to value 0"]
impl crate::Resettable for T_STRING_SPEC {}
