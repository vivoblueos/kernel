#[doc = "Register `STATUS_NEXT` reader"]
pub type R = crate::R<STATUS_NEXT_SPEC>;
#[doc = "Field `STATUS_INTERRUPT_NEXT` reader - GPIO interrupt source register for GPIO0-31"]
pub type STATUS_INTERRUPT_NEXT_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - GPIO interrupt source register for GPIO0-31"]
    #[inline(always)]
    pub fn status_interrupt_next(&self) -> STATUS_INTERRUPT_NEXT_R {
        STATUS_INTERRUPT_NEXT_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("STATUS_NEXT")
            .field("status_interrupt_next", &self.status_interrupt_next())
            .finish()
    }
}
#[doc = "GPIO interrupt source register for GPIO0-31\n\nYou can [`read`](crate::Reg::read) this register and get [`status_next::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct STATUS_NEXT_SPEC;
impl crate::RegisterSpec for STATUS_NEXT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`status_next::R`](R) reader structure"]
impl crate::Readable for STATUS_NEXT_SPEC {}
#[doc = "`reset()` method sets STATUS_NEXT to value 0"]
impl crate::Resettable for STATUS_NEXT_SPEC {}
