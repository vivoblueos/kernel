#[doc = "Register `SAR1DATA_STATUS` reader"]
pub type R = crate::R<SAR1DATA_STATUS_SPEC>;
#[doc = "Field `SARADC1_DATA` reader - saradc1 data"]
pub type SARADC1_DATA_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:16 - saradc1 data"]
    #[inline(always)]
    pub fn saradc1_data(&self) -> SARADC1_DATA_R {
        SARADC1_DATA_R::new(self.bits & 0x0001_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SAR1DATA_STATUS")
            .field("saradc1_data", &self.saradc1_data())
            .finish()
    }
}
#[doc = "digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`sar1data_status::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SAR1DATA_STATUS_SPEC;
impl crate::RegisterSpec for SAR1DATA_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sar1data_status::R`](R) reader structure"]
impl crate::Readable for SAR1DATA_STATUS_SPEC {}
#[doc = "`reset()` method sets SAR1DATA_STATUS to value 0"]
impl crate::Resettable for SAR1DATA_STATUS_SPEC {}
