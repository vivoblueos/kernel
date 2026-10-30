#[doc = "Register `SP_MIN` reader"]
pub type R = crate::R<SP_MIN_SPEC>;
#[doc = "Register `SP_MIN` writer"]
pub type W = crate::W<SP_MIN_SPEC>;
#[doc = "Field `SP_MIN` reader - core0 sp region configuration regsiter"]
pub type SP_MIN_R = crate::FieldReader<u32>;
#[doc = "Field `SP_MIN` writer - core0 sp region configuration regsiter"]
pub type SP_MIN_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - core0 sp region configuration regsiter"]
    #[inline(always)]
    pub fn sp_min(&self) -> SP_MIN_R {
        SP_MIN_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SP_MIN")
            .field("sp_min", &self.sp_min())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - core0 sp region configuration regsiter"]
    #[inline(always)]
    pub fn sp_min(&mut self) -> SP_MIN_W<'_, SP_MIN_SPEC> {
        SP_MIN_W::new(self, 0)
    }
}
#[doc = "stack min value\n\nYou can [`read`](crate::Reg::read) this register and get [`sp_min::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sp_min::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SP_MIN_SPEC;
impl crate::RegisterSpec for SP_MIN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sp_min::R`](R) reader structure"]
impl crate::Readable for SP_MIN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sp_min::W`](W) writer structure"]
impl crate::Writable for SP_MIN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SP_MIN to value 0"]
impl crate::Resettable for SP_MIN_SPEC {}
