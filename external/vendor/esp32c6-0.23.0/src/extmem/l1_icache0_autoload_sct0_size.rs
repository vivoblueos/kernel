#[doc = "Register `L1_ICACHE0_AUTOLOAD_SCT0_SIZE` reader"]
pub type R = crate::R<L1_ICACHE0_AUTOLOAD_SCT0_SIZE_SPEC>;
#[doc = "Field `L1_ICACHE0_AUTOLOAD_SCT0_SIZE` reader - Those bits are used to configure the size of the first section for autoload operation on L1-ICache0. Note that it should be used together with L1_ICACHE0_AUTOLOAD_SCT0_ADDR and L1_ICACHE_AUTOLOAD_SCT0_ENA."]
pub type L1_ICACHE0_AUTOLOAD_SCT0_SIZE_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:27 - Those bits are used to configure the size of the first section for autoload operation on L1-ICache0. Note that it should be used together with L1_ICACHE0_AUTOLOAD_SCT0_ADDR and L1_ICACHE_AUTOLOAD_SCT0_ENA."]
    #[inline(always)]
    pub fn l1_icache0_autoload_sct0_size(&self) -> L1_ICACHE0_AUTOLOAD_SCT0_SIZE_R {
        L1_ICACHE0_AUTOLOAD_SCT0_SIZE_R::new(self.bits & 0x0fff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_ICACHE0_AUTOLOAD_SCT0_SIZE")
            .field(
                "l1_icache0_autoload_sct0_size",
                &self.l1_icache0_autoload_sct0_size(),
            )
            .finish()
    }
}
#[doc = "L1 instruction Cache 0 autoload section 0 size configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_icache0_autoload_sct0_size::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_ICACHE0_AUTOLOAD_SCT0_SIZE_SPEC;
impl crate::RegisterSpec for L1_ICACHE0_AUTOLOAD_SCT0_SIZE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_icache0_autoload_sct0_size::R`](R) reader structure"]
impl crate::Readable for L1_ICACHE0_AUTOLOAD_SCT0_SIZE_SPEC {}
#[doc = "`reset()` method sets L1_ICACHE0_AUTOLOAD_SCT0_SIZE to value 0"]
impl crate::Resettable for L1_ICACHE0_AUTOLOAD_SCT0_SIZE_SPEC {}
