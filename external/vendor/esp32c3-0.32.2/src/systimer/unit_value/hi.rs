#[doc = "Register `HI` reader"]
pub type R = crate::R<HI_SPEC>;
#[doc = "Field `VALUE_HI` reader - timer read value high 32bit"]
pub type VALUE_HI_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:19 - timer read value high 32bit"]
    #[inline(always)]
    pub fn value_hi(&self) -> VALUE_HI_R {
        VALUE_HI_R::new(self.bits & 0x000f_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HI")
            .field("value_hi", &self.value_hi())
            .finish()
    }
}
#[doc = "SYSTIMER_UNIT0_VALUE_HI.\n\nYou can [`read`](crate::Reg::read) this register and get [`hi::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HI_SPEC;
impl crate::RegisterSpec for HI_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hi::R`](R) reader structure"]
impl crate::Readable for HI_SPEC {}
#[doc = "`reset()` method sets HI to value 0"]
impl crate::Resettable for HI_SPEC {}
