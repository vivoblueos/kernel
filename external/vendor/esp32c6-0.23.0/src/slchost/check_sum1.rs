#[doc = "Register `CHECK_SUM1` reader"]
pub type R = crate::R<CHECK_SUM1_SPEC>;
#[doc = "Field `SLCHOST_CHECK_SUM1` reader - *******Description***********"]
pub type SLCHOST_CHECK_SUM1_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_check_sum1(&self) -> SLCHOST_CHECK_SUM1_R {
        SLCHOST_CHECK_SUM1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CHECK_SUM1")
            .field("slchost_check_sum1", &self.slchost_check_sum1())
            .finish()
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`check_sum1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CHECK_SUM1_SPEC;
impl crate::RegisterSpec for CHECK_SUM1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`check_sum1::R`](R) reader structure"]
impl crate::Readable for CHECK_SUM1_SPEC {}
#[doc = "`reset()` method sets CHECK_SUM1 to value 0x013f"]
impl crate::Resettable for CHECK_SUM1_SPEC {
    const RESET_VALUE: u32 = 0x013f;
}
