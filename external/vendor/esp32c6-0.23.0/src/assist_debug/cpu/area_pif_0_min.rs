#[doc = "Register `AREA_PIF_0_MIN` reader"]
pub type R = crate::R<AREA_PIF_0_MIN_SPEC>;
#[doc = "Register `AREA_PIF_0_MIN` writer"]
pub type W = crate::W<AREA_PIF_0_MIN_SPEC>;
#[doc = "Field `AREA_PIF_0_MIN` reader - Core0 PIF region0 start addr"]
pub type AREA_PIF_0_MIN_R = crate::FieldReader<u32>;
#[doc = "Field `AREA_PIF_0_MIN` writer - Core0 PIF region0 start addr"]
pub type AREA_PIF_0_MIN_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Core0 PIF region0 start addr"]
    #[inline(always)]
    pub fn area_pif_0_min(&self) -> AREA_PIF_0_MIN_R {
        AREA_PIF_0_MIN_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("AREA_PIF_0_MIN")
            .field("area_pif_0_min", &self.area_pif_0_min())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Core0 PIF region0 start addr"]
    #[inline(always)]
    pub fn area_pif_0_min(&mut self) -> AREA_PIF_0_MIN_W<'_, AREA_PIF_0_MIN_SPEC> {
        AREA_PIF_0_MIN_W::new(self, 0)
    }
}
#[doc = "core0 PIF region0 addr configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`area_pif_0_min::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`area_pif_0_min::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AREA_PIF_0_MIN_SPEC;
impl crate::RegisterSpec for AREA_PIF_0_MIN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`area_pif_0_min::R`](R) reader structure"]
impl crate::Readable for AREA_PIF_0_MIN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`area_pif_0_min::W`](W) writer structure"]
impl crate::Writable for AREA_PIF_0_MIN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets AREA_PIF_0_MIN to value 0xffff_ffff"]
impl crate::Resettable for AREA_PIF_0_MIN_SPEC {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
