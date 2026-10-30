#[doc = "Register `LOG_MEM_FULL_FLAG` reader"]
pub type R = crate::R<LOG_MEM_FULL_FLAG_SPEC>;
#[doc = "Register `LOG_MEM_FULL_FLAG` writer"]
pub type W = crate::W<LOG_MEM_FULL_FLAG_SPEC>;
#[doc = "Field `LOG_MEM_FULL_FLAG` reader - reg_log_mem_full_flag"]
pub type LOG_MEM_FULL_FLAG_R = crate::BitReader;
#[doc = "Field `CLR_LOG_MEM_FULL_FLAG` reader - reg_clr_log_mem_full_flag"]
pub type CLR_LOG_MEM_FULL_FLAG_R = crate::BitReader;
#[doc = "Field `CLR_LOG_MEM_FULL_FLAG` writer - reg_clr_log_mem_full_flag"]
pub type CLR_LOG_MEM_FULL_FLAG_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - reg_log_mem_full_flag"]
    #[inline(always)]
    pub fn log_mem_full_flag(&self) -> LOG_MEM_FULL_FLAG_R {
        LOG_MEM_FULL_FLAG_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - reg_clr_log_mem_full_flag"]
    #[inline(always)]
    pub fn clr_log_mem_full_flag(&self) -> CLR_LOG_MEM_FULL_FLAG_R {
        CLR_LOG_MEM_FULL_FLAG_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LOG_MEM_FULL_FLAG")
            .field("log_mem_full_flag", &self.log_mem_full_flag())
            .field("clr_log_mem_full_flag", &self.clr_log_mem_full_flag())
            .finish()
    }
}
impl W {
    #[doc = "Bit 1 - reg_clr_log_mem_full_flag"]
    #[inline(always)]
    pub fn clr_log_mem_full_flag(&mut self) -> CLR_LOG_MEM_FULL_FLAG_W<'_, LOG_MEM_FULL_FLAG_SPEC> {
        CLR_LOG_MEM_FULL_FLAG_W::new(self, 1)
    }
}
#[doc = "ASSIST_DEBUG_LOG_MEM_FULL_FLAG_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`log_mem_full_flag::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_mem_full_flag::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LOG_MEM_FULL_FLAG_SPEC;
impl crate::RegisterSpec for LOG_MEM_FULL_FLAG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`log_mem_full_flag::R`](R) reader structure"]
impl crate::Readable for LOG_MEM_FULL_FLAG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`log_mem_full_flag::W`](W) writer structure"]
impl crate::Writable for LOG_MEM_FULL_FLAG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LOG_MEM_FULL_FLAG to value 0"]
impl crate::Resettable for LOG_MEM_FULL_FLAG_SPEC {}
