#[doc = "Register `STATE1` reader"]
pub type R = crate::R<STATE1_SPEC>;
#[doc = "Field `ENCODE_STATE` reader - a"]
pub type ENCODE_STATE_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:2 - a"]
    #[inline(always)]
    pub fn encode_state(&self) -> ENCODE_STATE_R {
        ENCODE_STATE_R::new((self.bits & 7) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("STATE1")
            .field("encode_state", &self.encode_state())
            .finish()
    }
}
#[doc = "a\n\nYou can [`read`](crate::Reg::read) this register and get [`state1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct STATE1_SPEC;
impl crate::RegisterSpec for STATE1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`state1::R`](R) reader structure"]
impl crate::Readable for STATE1_SPEC {}
#[doc = "`reset()` method sets STATE1 to value 0"]
impl crate::Resettable for STATE1_SPEC {}
