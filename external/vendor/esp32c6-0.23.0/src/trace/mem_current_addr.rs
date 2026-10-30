#[doc = "Register `MEM_CURRENT_ADDR` reader"]
pub type R = crate::R<MEM_CURRENT_ADDR_SPEC>;
#[doc = "Field `MEM_CURRENT_ADDR` reader - current_mem_addr,indicate that next writing addr"]
pub type MEM_CURRENT_ADDR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - current_mem_addr,indicate that next writing addr"]
    #[inline(always)]
    pub fn mem_current_addr(&self) -> MEM_CURRENT_ADDR_R {
        MEM_CURRENT_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MEM_CURRENT_ADDR")
            .field("mem_current_addr", &self.mem_current_addr())
            .finish()
    }
}
#[doc = "mem current addr\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_current_addr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MEM_CURRENT_ADDR_SPEC;
impl crate::RegisterSpec for MEM_CURRENT_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mem_current_addr::R`](R) reader structure"]
impl crate::Readable for MEM_CURRENT_ADDR_SPEC {}
#[doc = "`reset()` method sets MEM_CURRENT_ADDR to value 0"]
impl crate::Resettable for MEM_CURRENT_ADDR_SPEC {}
