#[doc = "Register `PAN_ID` reader"]
pub type R = crate::R<PAN_ID_SPEC>;
#[doc = "Register `PAN_ID` writer"]
pub type W = crate::W<PAN_ID_SPEC>;
#[doc = "Field `PAN_ID` reader - "]
pub type PAN_ID_R = crate::FieldReader<u16>;
#[doc = "Field `PAN_ID` writer - "]
pub type PAN_ID_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn pan_id(&self) -> PAN_ID_R {
        PAN_ID_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PAN_ID")
            .field("pan_id", &self.pan_id())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn pan_id(&mut self) -> PAN_ID_W<'_, PAN_ID_SPEC> {
        PAN_ID_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`pan_id::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pan_id::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PAN_ID_SPEC;
impl crate::RegisterSpec for PAN_ID_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pan_id::R`](R) reader structure"]
impl crate::Readable for PAN_ID_SPEC {}
#[doc = "`write(|w| ..)` method takes [`pan_id::W`](W) writer structure"]
impl crate::Writable for PAN_ID_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PAN_ID to value 0"]
impl crate::Resettable for PAN_ID_SPEC {}
