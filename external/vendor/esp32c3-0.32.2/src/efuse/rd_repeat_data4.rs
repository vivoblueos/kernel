#[doc = "Register `RD_REPEAT_DATA4` reader"]
pub type R = crate::R<RD_REPEAT_DATA4_SPEC>;
#[doc = "Field `RPT4_RESERVED4` reader - Reserved (used for four backups method)."]
pub type RPT4_RESERVED4_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:23 - Reserved (used for four backups method)."]
    #[inline(always)]
    pub fn rpt4_reserved4(&self) -> RPT4_RESERVED4_R {
        RPT4_RESERVED4_R::new(self.bits & 0x00ff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_REPEAT_DATA4")
            .field("rpt4_reserved4", &self.rpt4_reserved4())
            .finish()
    }
}
#[doc = "BLOCK0 data register 5.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_data4::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_REPEAT_DATA4_SPEC;
impl crate::RegisterSpec for RD_REPEAT_DATA4_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_repeat_data4::R`](R) reader structure"]
impl crate::Readable for RD_REPEAT_DATA4_SPEC {}
#[doc = "`reset()` method sets RD_REPEAT_DATA4 to value 0"]
impl crate::Resettable for RD_REPEAT_DATA4_SPEC {}
