#[doc = "Register `CORE_DUMMY_DATA` reader"]
pub type R = crate::R<CORE_DUMMY_DATA_SPEC>;
#[doc = "Register `CORE_DUMMY_DATA` writer"]
pub type W = crate::W<CORE_DUMMY_DATA_SPEC>;
#[doc = "Field `CORE_DUMMY_DATA` reader - "]
pub type CORE_DUMMY_DATA_R = crate::FieldReader<u32>;
#[doc = "Field `CORE_DUMMY_DATA` writer - "]
pub type CORE_DUMMY_DATA_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn core_dummy_data(&self) -> CORE_DUMMY_DATA_R {
        CORE_DUMMY_DATA_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE_DUMMY_DATA")
            .field("core_dummy_data", &self.core_dummy_data())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn core_dummy_data(&mut self) -> CORE_DUMMY_DATA_W<'_, CORE_DUMMY_DATA_SPEC> {
        CORE_DUMMY_DATA_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`core_dummy_data::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_dummy_data::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE_DUMMY_DATA_SPEC;
impl crate::RegisterSpec for CORE_DUMMY_DATA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core_dummy_data::R`](R) reader structure"]
impl crate::Readable for CORE_DUMMY_DATA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`core_dummy_data::W`](W) writer structure"]
impl crate::Writable for CORE_DUMMY_DATA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CORE_DUMMY_DATA to value 0"]
impl crate::Resettable for CORE_DUMMY_DATA_SPEC {}
