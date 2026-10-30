#[doc = "Register `RD_REPEAT_ERR4` reader"]
pub type R = crate::R<RD_REPEAT_ERR4_SPEC>;
#[doc = "Field `RPT4_RESERVED4_ERR` reader - Reserved."]
pub type RPT4_RESERVED4_ERR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:23 - Reserved."]
    #[inline(always)]
    pub fn rpt4_reserved4_err(&self) -> RPT4_RESERVED4_ERR_R {
        RPT4_RESERVED4_ERR_R::new(self.bits & 0x00ff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_REPEAT_ERR4")
            .field("rpt4_reserved4_err", &self.rpt4_reserved4_err())
            .finish()
    }
}
#[doc = "Programming error record register 4 of BLOCK0.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_err4::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_REPEAT_ERR4_SPEC;
impl crate::RegisterSpec for RD_REPEAT_ERR4_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_repeat_err4::R`](R) reader structure"]
impl crate::Readable for RD_REPEAT_ERR4_SPEC {}
#[doc = "`reset()` method sets RD_REPEAT_ERR4 to value 0"]
impl crate::Resettable for RD_REPEAT_ERR4_SPEC {}
