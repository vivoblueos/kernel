#[doc = "Register `L2_CACHE_SYNC_RST_CTRL` reader"]
pub type R = crate::R<L2_CACHE_SYNC_RST_CTRL_SPEC>;
#[doc = "Field `L2_CACHE_SYNC_RST` reader - set this bit to reset sync-logic inside L2-Cache. Recommend that this should only be used to initialize sync-logic when some fatal error of sync-logic occurs."]
pub type L2_CACHE_SYNC_RST_R = crate::BitReader;
impl R {
    #[doc = "Bit 5 - set this bit to reset sync-logic inside L2-Cache. Recommend that this should only be used to initialize sync-logic when some fatal error of sync-logic occurs."]
    #[inline(always)]
    pub fn l2_cache_sync_rst(&self) -> L2_CACHE_SYNC_RST_R {
        L2_CACHE_SYNC_RST_R::new(((self.bits >> 5) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L2_CACHE_SYNC_RST_CTRL")
            .field("l2_cache_sync_rst", &self.l2_cache_sync_rst())
            .finish()
    }
}
#[doc = "Cache Sync Reset control register\n\nYou can [`read`](crate::Reg::read) this register and get [`l2_cache_sync_rst_ctrl::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L2_CACHE_SYNC_RST_CTRL_SPEC;
impl crate::RegisterSpec for L2_CACHE_SYNC_RST_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l2_cache_sync_rst_ctrl::R`](R) reader structure"]
impl crate::Readable for L2_CACHE_SYNC_RST_CTRL_SPEC {}
#[doc = "`reset()` method sets L2_CACHE_SYNC_RST_CTRL to value 0"]
impl crate::Resettable for L2_CACHE_SYNC_RST_CTRL_SPEC {}
