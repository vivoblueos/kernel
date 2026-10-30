#[doc = "Register `LOG_MEM_WRITING_ADDR` reader"]
pub type R = crate::R<LOG_MEM_WRITING_ADDR_SPEC>;
#[doc = "Field `LOG_MEM_WRITING_ADDR` reader - reg_log_mem_writing_addr"]
pub type LOG_MEM_WRITING_ADDR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - reg_log_mem_writing_addr"]
    #[inline(always)]
    pub fn log_mem_writing_addr(&self) -> LOG_MEM_WRITING_ADDR_R {
        LOG_MEM_WRITING_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LOG_MEM_WRITING_ADDR")
            .field("log_mem_writing_addr", &self.log_mem_writing_addr())
            .finish()
    }
}
#[doc = "ASSIST_DEBUG_LOG_MEM_WRITING_ADDR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`log_mem_writing_addr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LOG_MEM_WRITING_ADDR_SPEC;
impl crate::RegisterSpec for LOG_MEM_WRITING_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`log_mem_writing_addr::R`](R) reader structure"]
impl crate::Readable for LOG_MEM_WRITING_ADDR_SPEC {}
#[doc = "`reset()` method sets LOG_MEM_WRITING_ADDR to value 0"]
impl crate::Resettable for LOG_MEM_WRITING_ADDR_SPEC {}
