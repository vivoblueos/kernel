#[doc = "Register `RD_SYS_PART2_DATA5` reader"]
pub type R = crate::R<RD_SYS_PART2_DATA5_SPEC>;
#[doc = "Field `SYS_DATA_PART2_5` reader - Stores the 5th 32 bits of the 2nd part of system data."]
pub type SYS_DATA_PART2_5_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Stores the 5th 32 bits of the 2nd part of system data."]
    #[inline(always)]
    pub fn sys_data_part2_5(&self) -> SYS_DATA_PART2_5_R {
        SYS_DATA_PART2_5_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_SYS_PART2_DATA5")
            .field("sys_data_part2_5", &self.sys_data_part2_5())
            .finish()
    }
}
#[doc = "Register 5 of BLOCK10 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part2_data5::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_SYS_PART2_DATA5_SPEC;
impl crate::RegisterSpec for RD_SYS_PART2_DATA5_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_sys_part2_data5::R`](R) reader structure"]
impl crate::Readable for RD_SYS_PART2_DATA5_SPEC {}
#[doc = "`reset()` method sets RD_SYS_PART2_DATA5 to value 0"]
impl crate::Resettable for RD_SYS_PART2_DATA5_SPEC {}
