#[doc = "Register `MTIME` reader"]
pub type R = crate::R<MTIME_SPEC>;
#[doc = "Register `MTIME` writer"]
pub type W = crate::W<MTIME_SPEC>;
#[doc = "Field `MTIME` reader - Configures the 64-bit CLINT timer counter value."]
pub type MTIME_R = crate::FieldReader<u64>;
#[doc = "Field `MTIME` writer - Configures the 64-bit CLINT timer counter value."]
pub type MTIME_W<'a, REG> = crate::FieldWriter<'a, REG, 64, u64>;
impl R {
    #[doc = "Bits 0:63 - Configures the 64-bit CLINT timer counter value."]
    #[inline(always)]
    pub fn mtime(&self) -> MTIME_R {
        MTIME_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MTIME")
            .field("mtime", &self.mtime())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:63 - Configures the 64-bit CLINT timer counter value."]
    #[inline(always)]
    pub fn mtime(&mut self) -> MTIME_W<'_, MTIME_SPEC> {
        MTIME_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`mtime::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mtime::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MTIME_SPEC;
impl crate::RegisterSpec for MTIME_SPEC {
    type Ux = u64;
}
#[doc = "`read()` method returns [`mtime::R`](R) reader structure"]
impl crate::Readable for MTIME_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mtime::W`](W) writer structure"]
impl crate::Writable for MTIME_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MTIME to value 0"]
impl crate::Resettable for MTIME_SPEC {}
