#[doc = "Register `MULT_INT_RAW` reader"]
pub type R = crate::R<MULT_INT_RAW_SPEC>;
#[doc = "Field `CALC_DONE` reader - The raw interrupt status bit for the ecc_calc_done_int interrupt"]
pub type CALC_DONE_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The raw interrupt status bit for the ecc_calc_done_int interrupt"]
    #[inline(always)]
    pub fn calc_done(&self) -> CALC_DONE_R {
        CALC_DONE_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MULT_INT_RAW")
            .field("calc_done", &self.calc_done())
            .finish()
    }
}
#[doc = "ECC interrupt raw register, valid in level.\n\nYou can [`read`](crate::Reg::read) this register and get [`mult_int_raw::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MULT_INT_RAW_SPEC;
impl crate::RegisterSpec for MULT_INT_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mult_int_raw::R`](R) reader structure"]
impl crate::Readable for MULT_INT_RAW_SPEC {}
#[doc = "`reset()` method sets MULT_INT_RAW to value 0"]
impl crate::Resettable for MULT_INT_RAW_SPEC {}
