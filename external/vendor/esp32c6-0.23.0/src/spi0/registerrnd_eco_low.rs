#[doc = "Register `REGISTERRND_ECO_LOW` reader"]
pub type R = crate::R<REGISTERRND_ECO_LOW_SPEC>;
#[doc = "Field `REGISTERRND_ECO_LOW` reader - ECO low register"]
pub type REGISTERRND_ECO_LOW_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - ECO low register"]
    #[inline(always)]
    pub fn registerrnd_eco_low(&self) -> REGISTERRND_ECO_LOW_R {
        REGISTERRND_ECO_LOW_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("REGISTERRND_ECO_LOW")
            .field("registerrnd_eco_low", &self.registerrnd_eco_low())
            .finish()
    }
}
#[doc = "MSPI ECO low register\n\nYou can [`read`](crate::Reg::read) this register and get [`registerrnd_eco_low::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REGISTERRND_ECO_LOW_SPEC;
impl crate::RegisterSpec for REGISTERRND_ECO_LOW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`registerrnd_eco_low::R`](R) reader structure"]
impl crate::Readable for REGISTERRND_ECO_LOW_SPEC {}
#[doc = "`reset()` method sets REGISTERRND_ECO_LOW to value 0x037c"]
impl crate::Resettable for REGISTERRND_ECO_LOW_SPEC {
    const RESET_VALUE: u32 = 0x037c;
}
