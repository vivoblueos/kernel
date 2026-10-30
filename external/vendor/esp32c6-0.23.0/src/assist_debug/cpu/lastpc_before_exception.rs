#[doc = "Register `LASTPC_BEFORE_EXCEPTION` reader"]
pub type R = crate::R<LASTPC_BEFORE_EXCEPTION_SPEC>;
#[doc = "Field `LASTPC_BEFORE_EXC` reader - cpu's lastpc before exception"]
pub type LASTPC_BEFORE_EXC_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - cpu's lastpc before exception"]
    #[inline(always)]
    pub fn lastpc_before_exc(&self) -> LASTPC_BEFORE_EXC_R {
        LASTPC_BEFORE_EXC_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LASTPC_BEFORE_EXCEPTION")
            .field("lastpc_before_exc", &self.lastpc_before_exc())
            .finish()
    }
}
#[doc = "ASSIST_DEBUG_CORE_0_LASTPC_BEFORE_EXCEPTION\n\nYou can [`read`](crate::Reg::read) this register and get [`lastpc_before_exception::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LASTPC_BEFORE_EXCEPTION_SPEC;
impl crate::RegisterSpec for LASTPC_BEFORE_EXCEPTION_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lastpc_before_exception::R`](R) reader structure"]
impl crate::Readable for LASTPC_BEFORE_EXCEPTION_SPEC {}
#[doc = "`reset()` method sets LASTPC_BEFORE_EXCEPTION to value 0"]
impl crate::Resettable for LASTPC_BEFORE_EXCEPTION_SPEC {}
