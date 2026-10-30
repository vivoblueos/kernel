#[doc = "Register `ERR_CODE_CAP` reader"]
pub type R = crate::R<ERR_CODE_CAP_SPEC>;
#[doc = "Field `ECC_SEGMENT` reader - This register contains information about the location of errors, see Table 181 for details."]
pub type ECC_SEGMENT_R = crate::FieldReader;
#[doc = "Field `ECC_DIRECTION` reader - This register contains information about transmission direction of the node when error occurs. 1: Error occurs when receiving a message; 0: Error occurs when transmitting a message"]
pub type ECC_DIRECTION_R = crate::BitReader;
#[doc = "Field `ECC_TYPE` reader - This register contains information about error types: 00: bit error; 01: form error; 10: stuff error; 11: other type of error"]
pub type ECC_TYPE_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:4 - This register contains information about the location of errors, see Table 181 for details."]
    #[inline(always)]
    pub fn ecc_segment(&self) -> ECC_SEGMENT_R {
        ECC_SEGMENT_R::new((self.bits & 0x1f) as u8)
    }
    #[doc = "Bit 5 - This register contains information about transmission direction of the node when error occurs. 1: Error occurs when receiving a message; 0: Error occurs when transmitting a message"]
    #[inline(always)]
    pub fn ecc_direction(&self) -> ECC_DIRECTION_R {
        ECC_DIRECTION_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bits 6:7 - This register contains information about error types: 00: bit error; 01: form error; 10: stuff error; 11: other type of error"]
    #[inline(always)]
    pub fn ecc_type(&self) -> ECC_TYPE_R {
        ECC_TYPE_R::new(((self.bits >> 6) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ERR_CODE_CAP")
            .field("ecc_segment", &self.ecc_segment())
            .field("ecc_direction", &self.ecc_direction())
            .field("ecc_type", &self.ecc_type())
            .finish()
    }
}
#[doc = "Error Code Capture Register\n\nYou can [`read`](crate::Reg::read) this register and get [`err_code_cap::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ERR_CODE_CAP_SPEC;
impl crate::RegisterSpec for ERR_CODE_CAP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`err_code_cap::R`](R) reader structure"]
impl crate::Readable for ERR_CODE_CAP_SPEC {}
#[doc = "`reset()` method sets ERR_CODE_CAP to value 0"]
impl crate::Resettable for ERR_CODE_CAP_SPEC {}
