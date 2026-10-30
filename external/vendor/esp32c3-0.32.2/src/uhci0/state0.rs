#[doc = "Register `STATE0` reader"]
pub type R = crate::R<STATE0_SPEC>;
#[doc = "Field `RX_ERR_CAUSE` reader - a"]
pub type RX_ERR_CAUSE_R = crate::FieldReader;
#[doc = "Field `DECODE_STATE` reader - a"]
pub type DECODE_STATE_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:2 - a"]
    #[inline(always)]
    pub fn rx_err_cause(&self) -> RX_ERR_CAUSE_R {
        RX_ERR_CAUSE_R::new((self.bits & 7) as u8)
    }
    #[doc = "Bits 3:5 - a"]
    #[inline(always)]
    pub fn decode_state(&self) -> DECODE_STATE_R {
        DECODE_STATE_R::new(((self.bits >> 3) & 7) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("STATE0")
            .field("rx_err_cause", &self.rx_err_cause())
            .field("decode_state", &self.decode_state())
            .finish()
    }
}
#[doc = "a\n\nYou can [`read`](crate::Reg::read) this register and get [`state0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct STATE0_SPEC;
impl crate::RegisterSpec for STATE0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`state0::R`](R) reader structure"]
impl crate::Readable for STATE0_SPEC {}
#[doc = "`reset()` method sets STATE0 to value 0"]
impl crate::Resettable for STATE0_SPEC {}
