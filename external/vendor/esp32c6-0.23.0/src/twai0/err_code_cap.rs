#[doc = "Register `ERR_CODE_CAP` reader"]
pub type R = crate::R<ERR_CODE_CAP_SPEC>;
#[doc = "Field `ERR_CAPTURE_CODE_SEGMENT` reader - This register contains information about the location of errors on the bus."]
pub type ERR_CAPTURE_CODE_SEGMENT_R = crate::FieldReader;
#[doc = "Field `ECC_DIRECTION` reader - 1: RX, error occurred during reception. 0: TX, error occurred during transmission."]
pub type ECC_DIRECTION_R = crate::BitReader;
#[doc = "Field `ERR_CAPTURE_CODE_TYPE` reader - 00: bit error. 01: form error. 10:stuff error. 11:other type of error."]
pub type ERR_CAPTURE_CODE_TYPE_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:4 - This register contains information about the location of errors on the bus."]
    #[inline(always)]
    pub fn err_capture_code_segment(&self) -> ERR_CAPTURE_CODE_SEGMENT_R {
        ERR_CAPTURE_CODE_SEGMENT_R::new((self.bits & 0x1f) as u8)
    }
    #[doc = "Bit 5 - 1: RX, error occurred during reception. 0: TX, error occurred during transmission."]
    #[inline(always)]
    pub fn ecc_direction(&self) -> ECC_DIRECTION_R {
        ECC_DIRECTION_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bits 6:7 - 00: bit error. 01: form error. 10:stuff error. 11:other type of error."]
    #[inline(always)]
    pub fn err_capture_code_type(&self) -> ERR_CAPTURE_CODE_TYPE_R {
        ERR_CAPTURE_CODE_TYPE_R::new(((self.bits >> 6) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ERR_CODE_CAP")
            .field("err_capture_code_segment", &self.err_capture_code_segment())
            .field("ecc_direction", &self.ecc_direction())
            .field("err_capture_code_type", &self.err_capture_code_type())
            .finish()
    }
}
#[doc = "TWAI error info capture register.\n\nYou can [`read`](crate::Reg::read) this register and get [`err_code_cap::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ERR_CODE_CAP_SPEC;
impl crate::RegisterSpec for ERR_CODE_CAP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`err_code_cap::R`](R) reader structure"]
impl crate::Readable for ERR_CODE_CAP_SPEC {}
#[doc = "`reset()` method sets ERR_CODE_CAP to value 0"]
impl crate::Resettable for ERR_CODE_CAP_SPEC {}
