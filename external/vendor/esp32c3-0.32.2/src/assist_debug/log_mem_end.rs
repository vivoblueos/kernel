#[doc = "Register `LOG_MEM_END` reader"]
pub type R = crate::R<LOG_MEM_END_SPEC>;
#[doc = "Register `LOG_MEM_END` writer"]
pub type W = crate::W<LOG_MEM_END_SPEC>;
#[doc = "Field `LOG_MEM_END` reader - reg_log_mem_end"]
pub type LOG_MEM_END_R = crate::FieldReader<u32>;
#[doc = "Field `LOG_MEM_END` writer - reg_log_mem_end"]
pub type LOG_MEM_END_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - reg_log_mem_end"]
    #[inline(always)]
    pub fn log_mem_end(&self) -> LOG_MEM_END_R {
        LOG_MEM_END_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LOG_MEM_END")
            .field("log_mem_end", &self.log_mem_end())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - reg_log_mem_end"]
    #[inline(always)]
    pub fn log_mem_end(&mut self) -> LOG_MEM_END_W<'_, LOG_MEM_END_SPEC> {
        LOG_MEM_END_W::new(self, 0)
    }
}
#[doc = "ASSIST_DEBUG_LOG_MEM_END_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`log_mem_end::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_mem_end::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LOG_MEM_END_SPEC;
impl crate::RegisterSpec for LOG_MEM_END_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`log_mem_end::R`](R) reader structure"]
impl crate::Readable for LOG_MEM_END_SPEC {}
#[doc = "`write(|w| ..)` method takes [`log_mem_end::W`](W) writer structure"]
impl crate::Writable for LOG_MEM_END_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LOG_MEM_END to value 0"]
impl crate::Resettable for LOG_MEM_END_SPEC {}
