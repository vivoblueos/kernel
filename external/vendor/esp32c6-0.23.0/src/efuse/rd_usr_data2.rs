#[doc = "Register `RD_USR_DATA2` reader"]
pub type R = crate::R<RD_USR_DATA2_SPEC>;
#[doc = "Field `USR_DATA2` reader - Stores the second 32 bits of BLOCK3 (user)."]
pub type USR_DATA2_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Stores the second 32 bits of BLOCK3 (user)."]
    #[inline(always)]
    pub fn usr_data2(&self) -> USR_DATA2_R {
        USR_DATA2_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_USR_DATA2")
            .field("usr_data2", &self.usr_data2())
            .finish()
    }
}
#[doc = "Register $n of BLOCK3 (user).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_usr_data2::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_USR_DATA2_SPEC;
impl crate::RegisterSpec for RD_USR_DATA2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_usr_data2::R`](R) reader structure"]
impl crate::Readable for RD_USR_DATA2_SPEC {}
#[doc = "`reset()` method sets RD_USR_DATA2 to value 0"]
impl crate::Resettable for RD_USR_DATA2_SPEC {}
