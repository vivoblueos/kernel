#[doc = "Register `CACHE_STATE` reader"]
pub type R = crate::R<CACHE_STATE_SPEC>;
#[doc = "Field `ICACHE_STATE` reader - The bit is used to indicate whether icache main fsm is in idle state or not. 1: in idle state, 0: not in idle state"]
pub type ICACHE_STATE_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:11 - The bit is used to indicate whether icache main fsm is in idle state or not. 1: in idle state, 0: not in idle state"]
    #[inline(always)]
    pub fn icache_state(&self) -> ICACHE_STATE_R {
        ICACHE_STATE_R::new((self.bits & 0x0fff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_STATE")
            .field("icache_state", &self.icache_state())
            .finish()
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_state::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_STATE_SPEC;
impl crate::RegisterSpec for CACHE_STATE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_state::R`](R) reader structure"]
impl crate::Readable for CACHE_STATE_SPEC {}
#[doc = "`reset()` method sets CACHE_STATE to value 0x01"]
impl crate::Resettable for CACHE_STATE_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
