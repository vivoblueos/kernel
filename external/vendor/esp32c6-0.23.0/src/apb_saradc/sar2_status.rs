#[doc = "Register `SAR2_STATUS` reader"]
pub type R = crate::R<SAR2_STATUS_SPEC>;
#[doc = "Field `SAR2_STATUS` reader - saradc2 status about data and channel"]
pub type SAR2_STATUS_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - saradc2 status about data and channel"]
    #[inline(always)]
    pub fn sar2_status(&self) -> SAR2_STATUS_R {
        SAR2_STATUS_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SAR2_STATUS")
            .field("sar2_status", &self.sar2_status())
            .finish()
    }
}
#[doc = "digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`sar2_status::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SAR2_STATUS_SPEC;
impl crate::RegisterSpec for SAR2_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sar2_status::R`](R) reader structure"]
impl crate::Readable for SAR2_STATUS_SPEC {}
#[doc = "`reset()` method sets SAR2_STATUS to value 0x2000_0000"]
impl crate::Resettable for SAR2_STATUS_SPEC {
    const RESET_VALUE: u32 = 0x2000_0000;
}
