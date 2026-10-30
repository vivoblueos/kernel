#[doc = "Register `IN1` reader"]
pub type R = crate::R<IN1_SPEC>;
#[doc = "Field `DATA_NEXT` reader - GPIO input register for GPIO32-34"]
pub type DATA_NEXT_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:2 - GPIO input register for GPIO32-34"]
    #[inline(always)]
    pub fn data_next(&self) -> DATA_NEXT_R {
        DATA_NEXT_R::new((self.bits & 7) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IN1")
            .field("data_next", &self.data_next())
            .finish()
    }
}
#[doc = "GPIO input register for GPIO32-34\n\nYou can [`read`](crate::Reg::read) this register and get [`in1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IN1_SPEC;
impl crate::RegisterSpec for IN1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`in1::R`](R) reader structure"]
impl crate::Readable for IN1_SPEC {}
#[doc = "`reset()` method sets IN1 to value 0"]
impl crate::Resettable for IN1_SPEC {}
