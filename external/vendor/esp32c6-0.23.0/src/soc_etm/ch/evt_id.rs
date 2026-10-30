#[doc = "Register `EVT_ID` reader"]
pub type R = crate::R<EVT_ID_SPEC>;
#[doc = "Register `EVT_ID` writer"]
pub type W = crate::W<EVT_ID_SPEC>;
#[doc = "Field `EVT_ID` reader - ch0_evt_id"]
pub type EVT_ID_R = crate::FieldReader;
#[doc = "Field `EVT_ID` writer - ch0_evt_id"]
pub type EVT_ID_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - ch0_evt_id"]
    #[inline(always)]
    pub fn evt_id(&self) -> EVT_ID_R {
        EVT_ID_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("EVT_ID")
            .field("evt_id", &self.evt_id())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - ch0_evt_id"]
    #[inline(always)]
    pub fn evt_id(&mut self) -> EVT_ID_W<'_, EVT_ID_SPEC> {
        EVT_ID_W::new(self, 0)
    }
}
#[doc = "channel0 event id register\n\nYou can [`read`](crate::Reg::read) this register and get [`evt_id::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`evt_id::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct EVT_ID_SPEC;
impl crate::RegisterSpec for EVT_ID_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`evt_id::R`](R) reader structure"]
impl crate::Readable for EVT_ID_SPEC {}
#[doc = "`write(|w| ..)` method takes [`evt_id::W`](W) writer structure"]
impl crate::Writable for EVT_ID_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets EVT_ID to value 0"]
impl crate::Resettable for EVT_ID_SPEC {}
