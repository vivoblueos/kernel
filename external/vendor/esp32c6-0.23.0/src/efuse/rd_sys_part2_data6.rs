#[doc = "Register `RD_SYS_PART2_DATA6` reader"]
pub type R = crate::R<RD_SYS_PART2_DATA6_SPEC>;
#[doc = "Field `SYS_DATA_PART2_6` reader - Stores the 0th 32 bits of the 2nd part of system data."]
pub type SYS_DATA_PART2_6_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Stores the 0th 32 bits of the 2nd part of system data."]
    #[inline(always)]
    pub fn sys_data_part2_6(&self) -> SYS_DATA_PART2_6_R {
        SYS_DATA_PART2_6_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_SYS_PART2_DATA6")
            .field("sys_data_part2_6", &self.sys_data_part2_6())
            .finish()
    }
}
#[doc = "Register $n of BLOCK10 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part2_data6::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_SYS_PART2_DATA6_SPEC;
impl crate::RegisterSpec for RD_SYS_PART2_DATA6_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_sys_part2_data6::R`](R) reader structure"]
impl crate::Readable for RD_SYS_PART2_DATA6_SPEC {}
#[doc = "`reset()` method sets RD_SYS_PART2_DATA6 to value 0"]
impl crate::Resettable for RD_SYS_PART2_DATA6_SPEC {}
