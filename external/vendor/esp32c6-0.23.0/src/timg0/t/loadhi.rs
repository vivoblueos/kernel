#[doc = "Register `LOADHI` reader"]
pub type R = crate::R<LOADHI_SPEC>;
#[doc = "Register `LOADHI` writer"]
pub type W = crate::W<LOADHI_SPEC>;
#[doc = "Field `LOAD_HI` reader - High 22 bits of the value that a reload will load onto timer %s time-base counter."]
pub type LOAD_HI_R = crate::FieldReader<u32>;
#[doc = "Field `LOAD_HI` writer - High 22 bits of the value that a reload will load onto timer %s time-base counter."]
pub type LOAD_HI_W<'a, REG> = crate::FieldWriter<'a, REG, 22, u32>;
impl R {
    #[doc = "Bits 0:21 - High 22 bits of the value that a reload will load onto timer %s time-base counter."]
    #[inline(always)]
    pub fn load_hi(&self) -> LOAD_HI_R {
        LOAD_HI_R::new(self.bits & 0x003f_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LOADHI")
            .field("load_hi", &self.load_hi())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:21 - High 22 bits of the value that a reload will load onto timer %s time-base counter."]
    #[inline(always)]
    pub fn load_hi(&mut self) -> LOAD_HI_W<'_, LOADHI_SPEC> {
        LOAD_HI_W::new(self, 0)
    }
}
#[doc = "Timer %s reload value, high 22 bits\n\nYou can [`read`](crate::Reg::read) this register and get [`loadhi::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`loadhi::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LOADHI_SPEC;
impl crate::RegisterSpec for LOADHI_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`loadhi::R`](R) reader structure"]
impl crate::Readable for LOADHI_SPEC {}
#[doc = "`write(|w| ..)` method takes [`loadhi::W`](W) writer structure"]
impl crate::Writable for LOADHI_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LOADHI to value 0"]
impl crate::Resettable for LOADHI_SPEC {}
