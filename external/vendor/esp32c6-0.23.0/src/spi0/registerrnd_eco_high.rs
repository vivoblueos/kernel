#[doc = "Register `REGISTERRND_ECO_HIGH` reader"]
pub type R = crate::R<REGISTERRND_ECO_HIGH_SPEC>;
#[doc = "Field `REGISTERRND_ECO_HIGH` reader - ECO high register"]
pub type REGISTERRND_ECO_HIGH_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - ECO high register"]
    #[inline(always)]
    pub fn registerrnd_eco_high(&self) -> REGISTERRND_ECO_HIGH_R {
        REGISTERRND_ECO_HIGH_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("REGISTERRND_ECO_HIGH")
            .field("registerrnd_eco_high", &self.registerrnd_eco_high())
            .finish()
    }
}
#[doc = "MSPI ECO high register\n\nYou can [`read`](crate::Reg::read) this register and get [`registerrnd_eco_high::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REGISTERRND_ECO_HIGH_SPEC;
impl crate::RegisterSpec for REGISTERRND_ECO_HIGH_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`registerrnd_eco_high::R`](R) reader structure"]
impl crate::Readable for REGISTERRND_ECO_HIGH_SPEC {}
#[doc = "`reset()` method sets REGISTERRND_ECO_HIGH to value 0x037c"]
impl crate::Resettable for REGISTERRND_ECO_HIGH_SPEC {
    const RESET_VALUE: u32 = 0x037c;
}
