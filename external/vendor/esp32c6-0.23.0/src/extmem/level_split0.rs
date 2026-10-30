#[doc = "Register `LEVEL_SPLIT0` reader"]
pub type R = crate::R<LEVEL_SPLIT0_SPEC>;
#[doc = "Field `LEVEL_SPLIT0` reader - Reserved"]
pub type LEVEL_SPLIT0_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Reserved"]
    #[inline(always)]
    pub fn level_split0(&self) -> LEVEL_SPLIT0_R {
        LEVEL_SPLIT0_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LEVEL_SPLIT0")
            .field("level_split0", &self.level_split0())
            .finish()
    }
}
#[doc = "USED TO SPLIT L1 CACHE AND L2 CACHE\n\nYou can [`read`](crate::Reg::read) this register and get [`level_split0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LEVEL_SPLIT0_SPEC;
impl crate::RegisterSpec for LEVEL_SPLIT0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`level_split0::R`](R) reader structure"]
impl crate::Readable for LEVEL_SPLIT0_SPEC {}
#[doc = "`reset()` method sets LEVEL_SPLIT0 to value 0x0258"]
impl crate::Resettable for LEVEL_SPLIT0_SPEC {
    const RESET_VALUE: u32 = 0x0258;
}
