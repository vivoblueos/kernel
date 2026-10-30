#[doc = "Register `AREA_DRAM0_1_MIN` reader"]
pub type R = crate::R<AREA_DRAM0_1_MIN_SPEC>;
#[doc = "Register `AREA_DRAM0_1_MIN` writer"]
pub type W = crate::W<AREA_DRAM0_1_MIN_SPEC>;
#[doc = "Field `AREA_DRAM0_1_MIN` reader - reg_core_0_area_dram0_1_min"]
pub type AREA_DRAM0_1_MIN_R = crate::FieldReader<u32>;
#[doc = "Field `AREA_DRAM0_1_MIN` writer - reg_core_0_area_dram0_1_min"]
pub type AREA_DRAM0_1_MIN_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - reg_core_0_area_dram0_1_min"]
    #[inline(always)]
    pub fn area_dram0_1_min(&self) -> AREA_DRAM0_1_MIN_R {
        AREA_DRAM0_1_MIN_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("AREA_DRAM0_1_MIN")
            .field("area_dram0_1_min", &self.area_dram0_1_min())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - reg_core_0_area_dram0_1_min"]
    #[inline(always)]
    pub fn area_dram0_1_min(&mut self) -> AREA_DRAM0_1_MIN_W<'_, AREA_DRAM0_1_MIN_SPEC> {
        AREA_DRAM0_1_MIN_W::new(self, 0)
    }
}
#[doc = "ASSIST_DEBUG_CORE_0_AREA_DRAM0_1_MIN_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`area_dram0_1_min::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`area_dram0_1_min::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AREA_DRAM0_1_MIN_SPEC;
impl crate::RegisterSpec for AREA_DRAM0_1_MIN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`area_dram0_1_min::R`](R) reader structure"]
impl crate::Readable for AREA_DRAM0_1_MIN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`area_dram0_1_min::W`](W) writer structure"]
impl crate::Writable for AREA_DRAM0_1_MIN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets AREA_DRAM0_1_MIN to value 0xffff_ffff"]
impl crate::Resettable for AREA_DRAM0_1_MIN_SPEC {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
