#[doc = "Register `LOG_DATA_MASK` reader"]
pub type R = crate::R<LOG_DATA_MASK_SPEC>;
#[doc = "Register `LOG_DATA_MASK` writer"]
pub type W = crate::W<LOG_DATA_MASK_SPEC>;
#[doc = "Field `LOG_DATA_SIZE` reader - reg_log_data_size"]
pub type LOG_DATA_SIZE_R = crate::FieldReader<u16>;
#[doc = "Field `LOG_DATA_SIZE` writer - reg_log_data_size"]
pub type LOG_DATA_SIZE_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - reg_log_data_size"]
    #[inline(always)]
    pub fn log_data_size(&self) -> LOG_DATA_SIZE_R {
        LOG_DATA_SIZE_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LOG_DATA_MASK")
            .field("log_data_size", &self.log_data_size())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - reg_log_data_size"]
    #[inline(always)]
    pub fn log_data_size(&mut self) -> LOG_DATA_SIZE_W<'_, LOG_DATA_MASK_SPEC> {
        LOG_DATA_SIZE_W::new(self, 0)
    }
}
#[doc = "ASSIST_DEBUG_LOG_DATA_MASK_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`log_data_mask::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_data_mask::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LOG_DATA_MASK_SPEC;
impl crate::RegisterSpec for LOG_DATA_MASK_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`log_data_mask::R`](R) reader structure"]
impl crate::Readable for LOG_DATA_MASK_SPEC {}
#[doc = "`write(|w| ..)` method takes [`log_data_mask::W`](W) writer structure"]
impl crate::Writable for LOG_DATA_MASK_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LOG_DATA_MASK to value 0"]
impl crate::Resettable for LOG_DATA_MASK_SPEC {}
