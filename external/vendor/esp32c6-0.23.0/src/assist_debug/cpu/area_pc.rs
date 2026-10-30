#[doc = "Register `AREA_PC` reader"]
pub type R = crate::R<AREA_PC_SPEC>;
#[doc = "Field `AREA_PC` reader - the stackpointer when first touch region monitor interrupt"]
pub type AREA_PC_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - the stackpointer when first touch region monitor interrupt"]
    #[inline(always)]
    pub fn area_pc(&self) -> AREA_PC_R {
        AREA_PC_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("AREA_PC")
            .field("area_pc", &self.area_pc())
            .finish()
    }
}
#[doc = "core0 area pc status register\n\nYou can [`read`](crate::Reg::read) this register and get [`area_pc::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AREA_PC_SPEC;
impl crate::RegisterSpec for AREA_PC_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`area_pc::R`](R) reader structure"]
impl crate::Readable for AREA_PC_SPEC {}
#[doc = "`reset()` method sets AREA_PC to value 0"]
impl crate::Resettable for AREA_PC_SPEC {}
