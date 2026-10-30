#[doc = "Register `CHECK_SUM0` reader"]
pub type R = crate::R<CHECK_SUM0_SPEC>;
#[doc = "Field `SLCHOST_CHECK_SUM0` reader - *******Description***********"]
pub type SLCHOST_CHECK_SUM0_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_check_sum0(&self) -> SLCHOST_CHECK_SUM0_R {
        SLCHOST_CHECK_SUM0_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CHECK_SUM0")
            .field("slchost_check_sum0", &self.slchost_check_sum0())
            .finish()
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`check_sum0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CHECK_SUM0_SPEC;
impl crate::RegisterSpec for CHECK_SUM0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`check_sum0::R`](R) reader structure"]
impl crate::Readable for CHECK_SUM0_SPEC {}
#[doc = "`reset()` method sets CHECK_SUM0 to value 0"]
impl crate::Resettable for CHECK_SUM0_SPEC {}
