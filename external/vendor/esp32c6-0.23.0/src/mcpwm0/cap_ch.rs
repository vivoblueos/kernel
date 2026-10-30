#[doc = "Register `CAP_CH%s` reader"]
pub type R = crate::R<CAP_CH_SPEC>;
#[doc = "Field `VALUE` reader - Value of last capture on channel 0"]
pub type VALUE_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Value of last capture on channel 0"]
    #[inline(always)]
    pub fn value(&self) -> VALUE_R {
        VALUE_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CAP_CH")
            .field("value", &self.value())
            .finish()
    }
}
#[doc = "Value of last capture on channel %s\n\nYou can [`read`](crate::Reg::read) this register and get [`cap_ch::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CAP_CH_SPEC;
impl crate::RegisterSpec for CAP_CH_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cap_ch::R`](R) reader structure"]
impl crate::Readable for CAP_CH_SPEC {}
#[doc = "`reset()` method sets CAP_CH%s to value 0"]
impl crate::Resettable for CAP_CH_SPEC {}
