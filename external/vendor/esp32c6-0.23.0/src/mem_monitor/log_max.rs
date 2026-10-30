#[doc = "Register `LOG_MAX` reader"]
pub type R = crate::R<LOG_MAX_SPEC>;
#[doc = "Register `LOG_MAX` writer"]
pub type W = crate::W<LOG_MAX_SPEC>;
#[doc = "Field `LOG_MAX` reader - the max address of log range"]
pub type LOG_MAX_R = crate::FieldReader<u32>;
#[doc = "Field `LOG_MAX` writer - the max address of log range"]
pub type LOG_MAX_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - the max address of log range"]
    #[inline(always)]
    pub fn log_max(&self) -> LOG_MAX_R {
        LOG_MAX_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LOG_MAX")
            .field("log_max", &self.log_max())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - the max address of log range"]
    #[inline(always)]
    pub fn log_max(&mut self) -> LOG_MAX_W<'_, LOG_MAX_SPEC> {
        LOG_MAX_W::new(self, 0)
    }
}
#[doc = "log boundary regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`log_max::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_max::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LOG_MAX_SPEC;
impl crate::RegisterSpec for LOG_MAX_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`log_max::R`](R) reader structure"]
impl crate::Readable for LOG_MAX_SPEC {}
#[doc = "`write(|w| ..)` method takes [`log_max::W`](W) writer structure"]
impl crate::Writable for LOG_MAX_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LOG_MAX to value 0"]
impl crate::Resettable for LOG_MAX_SPEC {}
