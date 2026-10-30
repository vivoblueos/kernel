#[doc = "Register `COMB_PVT_ERR_LVT_SITE0` reader"]
pub type R = crate::R<COMB_PVT_ERR_LVT_SITE0_SPEC>;
#[doc = "Field `ERR_CNT` reader - Error counter"]
pub type ERR_CNT_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - Error counter"]
    #[inline(always)]
    pub fn err_cnt(&self) -> ERR_CNT_R {
        ERR_CNT_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("COMB_PVT_ERR_LVT_SITE0")
            .field("err_cnt", &self.err_cnt())
            .finish()
    }
}
#[doc = "mem pvt register\n\nYou can [`read`](crate::Reg::read) this register and get [`comb_pvt_err_lvt_site0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct COMB_PVT_ERR_LVT_SITE0_SPEC;
impl crate::RegisterSpec for COMB_PVT_ERR_LVT_SITE0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`comb_pvt_err_lvt_site0::R`](R) reader structure"]
impl crate::Readable for COMB_PVT_ERR_LVT_SITE0_SPEC {}
#[doc = "`reset()` method sets COMB_PVT_ERR_LVT_SITE0 to value 0"]
impl crate::Resettable for COMB_PVT_ERR_LVT_SITE0_SPEC {}
