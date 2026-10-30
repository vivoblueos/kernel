#[doc = "Register `FRAM_NUM` reader"]
pub type R = crate::R<FRAM_NUM_SPEC>;
#[doc = "Field `SOF_FRAME_INDEX` reader - Frame index of received SOF frame."]
pub type SOF_FRAME_INDEX_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:10 - Frame index of received SOF frame."]
    #[inline(always)]
    pub fn sof_frame_index(&self) -> SOF_FRAME_INDEX_R {
        SOF_FRAME_INDEX_R::new((self.bits & 0x07ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FRAM_NUM")
            .field("sof_frame_index", &self.sof_frame_index())
            .finish()
    }
}
#[doc = "USB_DEVICE_FRAM_NUM_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`fram_num::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FRAM_NUM_SPEC;
impl crate::RegisterSpec for FRAM_NUM_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fram_num::R`](R) reader structure"]
impl crate::Readable for FRAM_NUM_SPEC {}
#[doc = "`reset()` method sets FRAM_NUM to value 0"]
impl crate::Resettable for FRAM_NUM_SPEC {}
