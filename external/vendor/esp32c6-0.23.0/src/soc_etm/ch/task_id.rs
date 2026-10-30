#[doc = "Register `TASK_ID` reader"]
pub type R = crate::R<TASK_ID_SPEC>;
#[doc = "Register `TASK_ID` writer"]
pub type W = crate::W<TASK_ID_SPEC>;
#[doc = "Field `TASK_ID` reader - ch0_task_id"]
pub type TASK_ID_R = crate::FieldReader;
#[doc = "Field `TASK_ID` writer - ch0_task_id"]
pub type TASK_ID_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - ch0_task_id"]
    #[inline(always)]
    pub fn task_id(&self) -> TASK_ID_R {
        TASK_ID_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TASK_ID")
            .field("task_id", &self.task_id())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - ch0_task_id"]
    #[inline(always)]
    pub fn task_id(&mut self) -> TASK_ID_W<'_, TASK_ID_SPEC> {
        TASK_ID_W::new(self, 0)
    }
}
#[doc = "channel0 task id register\n\nYou can [`read`](crate::Reg::read) this register and get [`task_id::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`task_id::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TASK_ID_SPEC;
impl crate::RegisterSpec for TASK_ID_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`task_id::R`](R) reader structure"]
impl crate::Readable for TASK_ID_SPEC {}
#[doc = "`write(|w| ..)` method takes [`task_id::W`](W) writer structure"]
impl crate::Writable for TASK_ID_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TASK_ID to value 0"]
impl crate::Resettable for TASK_ID_SPEC {}
