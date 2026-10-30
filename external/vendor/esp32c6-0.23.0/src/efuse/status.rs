#[doc = "Register `STATUS` reader"]
pub type R = crate::R<STATUS_SPEC>;
#[doc = "Field `STATE` reader - Indicates the state of the eFuse state machine."]
pub type STATE_R = crate::FieldReader;
#[doc = "Field `OTP_LOAD_SW` reader - The value of OTP_LOAD_SW."]
pub type OTP_LOAD_SW_R = crate::BitReader;
#[doc = "Field `OTP_VDDQ_C_SYNC2` reader - The value of OTP_VDDQ_C_SYNC2."]
pub type OTP_VDDQ_C_SYNC2_R = crate::BitReader;
#[doc = "Field `OTP_STROBE_SW` reader - The value of OTP_STROBE_SW."]
pub type OTP_STROBE_SW_R = crate::BitReader;
#[doc = "Field `OTP_CSB_SW` reader - The value of OTP_CSB_SW."]
pub type OTP_CSB_SW_R = crate::BitReader;
#[doc = "Field `OTP_PGENB_SW` reader - The value of OTP_PGENB_SW."]
pub type OTP_PGENB_SW_R = crate::BitReader;
#[doc = "Field `OTP_VDDQ_IS_SW` reader - The value of OTP_VDDQ_IS_SW."]
pub type OTP_VDDQ_IS_SW_R = crate::BitReader;
#[doc = "Field `BLK0_VALID_BIT_CNT` reader - Indicates the number of block valid bit."]
pub type BLK0_VALID_BIT_CNT_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:3 - Indicates the state of the eFuse state machine."]
    #[inline(always)]
    pub fn state(&self) -> STATE_R {
        STATE_R::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bit 4 - The value of OTP_LOAD_SW."]
    #[inline(always)]
    pub fn otp_load_sw(&self) -> OTP_LOAD_SW_R {
        OTP_LOAD_SW_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The value of OTP_VDDQ_C_SYNC2."]
    #[inline(always)]
    pub fn otp_vddq_c_sync2(&self) -> OTP_VDDQ_C_SYNC2_R {
        OTP_VDDQ_C_SYNC2_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The value of OTP_STROBE_SW."]
    #[inline(always)]
    pub fn otp_strobe_sw(&self) -> OTP_STROBE_SW_R {
        OTP_STROBE_SW_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The value of OTP_CSB_SW."]
    #[inline(always)]
    pub fn otp_csb_sw(&self) -> OTP_CSB_SW_R {
        OTP_CSB_SW_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The value of OTP_PGENB_SW."]
    #[inline(always)]
    pub fn otp_pgenb_sw(&self) -> OTP_PGENB_SW_R {
        OTP_PGENB_SW_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The value of OTP_VDDQ_IS_SW."]
    #[inline(always)]
    pub fn otp_vddq_is_sw(&self) -> OTP_VDDQ_IS_SW_R {
        OTP_VDDQ_IS_SW_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bits 10:19 - Indicates the number of block valid bit."]
    #[inline(always)]
    pub fn blk0_valid_bit_cnt(&self) -> BLK0_VALID_BIT_CNT_R {
        BLK0_VALID_BIT_CNT_R::new(((self.bits >> 10) & 0x03ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("STATUS")
            .field("state", &self.state())
            .field("otp_load_sw", &self.otp_load_sw())
            .field("otp_vddq_c_sync2", &self.otp_vddq_c_sync2())
            .field("otp_strobe_sw", &self.otp_strobe_sw())
            .field("otp_csb_sw", &self.otp_csb_sw())
            .field("otp_pgenb_sw", &self.otp_pgenb_sw())
            .field("otp_vddq_is_sw", &self.otp_vddq_is_sw())
            .field("blk0_valid_bit_cnt", &self.blk0_valid_bit_cnt())
            .finish()
    }
}
#[doc = "eFuse status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`status::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct STATUS_SPEC;
impl crate::RegisterSpec for STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`status::R`](R) reader structure"]
impl crate::Readable for STATUS_SPEC {}
#[doc = "`reset()` method sets STATUS to value 0"]
impl crate::Resettable for STATUS_SPEC {}
