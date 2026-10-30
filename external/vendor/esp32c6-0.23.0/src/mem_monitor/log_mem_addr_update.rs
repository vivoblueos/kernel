#[doc = "Register `LOG_MEM_ADDR_UPDATE` writer"]
pub type W = crate::W<LOG_MEM_ADDR_UPDATE_SPEC>;
#[doc = "Field `LOG_MEM_ADDR_UPDATE` writer - Set 1 to updata MEM_MONITOR_LOG_MEM_CURRENT_ADDR, when set 1, MEM_MONITOR_LOG_MEM_CURRENT_ADDR will update to MEM_MONITOR_LOG_MEM_START"]
pub type LOG_MEM_ADDR_UPDATE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<LOG_MEM_ADDR_UPDATE_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to updata MEM_MONITOR_LOG_MEM_CURRENT_ADDR, when set 1, MEM_MONITOR_LOG_MEM_CURRENT_ADDR will update to MEM_MONITOR_LOG_MEM_START"]
    #[inline(always)]
    pub fn log_mem_addr_update(&mut self) -> LOG_MEM_ADDR_UPDATE_W<'_, LOG_MEM_ADDR_UPDATE_SPEC> {
        LOG_MEM_ADDR_UPDATE_W::new(self, 0)
    }
}
#[doc = "writing address update\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_mem_addr_update::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LOG_MEM_ADDR_UPDATE_SPEC;
impl crate::RegisterSpec for LOG_MEM_ADDR_UPDATE_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`log_mem_addr_update::W`](W) writer structure"]
impl crate::Writable for LOG_MEM_ADDR_UPDATE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LOG_MEM_ADDR_UPDATE to value 0"]
impl crate::Resettable for LOG_MEM_ADDR_UPDATE_SPEC {}
