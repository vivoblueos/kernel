#[doc = "Register `L2_CACHE_PRELOAD_RST_CTRL` reader"]
pub type R = crate::R<L2_CACHE_PRELOAD_RST_CTRL_SPEC>;
#[doc = "Field `L2_CACHE_PLD_RST` reader - set this bit to reset preload-logic inside L2-Cache. Recommend that this should only be used to initialize preload-logic when some fatal error of preload-logic occurs."]
pub type L2_CACHE_PLD_RST_R = crate::BitReader;
impl R {
    #[doc = "Bit 5 - set this bit to reset preload-logic inside L2-Cache. Recommend that this should only be used to initialize preload-logic when some fatal error of preload-logic occurs."]
    #[inline(always)]
    pub fn l2_cache_pld_rst(&self) -> L2_CACHE_PLD_RST_R {
        L2_CACHE_PLD_RST_R::new(((self.bits >> 5) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L2_CACHE_PRELOAD_RST_CTRL")
            .field("l2_cache_pld_rst", &self.l2_cache_pld_rst())
            .finish()
    }
}
#[doc = "Cache Preload Reset control register\n\nYou can [`read`](crate::Reg::read) this register and get [`l2_cache_preload_rst_ctrl::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L2_CACHE_PRELOAD_RST_CTRL_SPEC;
impl crate::RegisterSpec for L2_CACHE_PRELOAD_RST_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l2_cache_preload_rst_ctrl::R`](R) reader structure"]
impl crate::Readable for L2_CACHE_PRELOAD_RST_CTRL_SPEC {}
#[doc = "`reset()` method sets L2_CACHE_PRELOAD_RST_CTRL to value 0"]
impl crate::Resettable for L2_CACHE_PRELOAD_RST_CTRL_SPEC {}
