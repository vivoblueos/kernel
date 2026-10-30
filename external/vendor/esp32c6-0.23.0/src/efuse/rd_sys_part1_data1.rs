#[doc = "Register `RD_SYS_PART1_DATA1` reader"]
pub type R = crate::R<RD_SYS_PART1_DATA1_SPEC>;
#[doc = "Field `SYS_DATA_PART1_1` reader - Stores the first 32 bits of the first part of system data."]
pub type SYS_DATA_PART1_1_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Stores the first 32 bits of the first part of system data."]
    #[inline(always)]
    pub fn sys_data_part1_1(&self) -> SYS_DATA_PART1_1_R {
        SYS_DATA_PART1_1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_SYS_PART1_DATA1")
            .field("sys_data_part1_1", &self.sys_data_part1_1())
            .finish()
    }
}
#[doc = "Register $n of BLOCK2 (system).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_sys_part1_data1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_SYS_PART1_DATA1_SPEC;
impl crate::RegisterSpec for RD_SYS_PART1_DATA1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_sys_part1_data1::R`](R) reader structure"]
impl crate::Readable for RD_SYS_PART1_DATA1_SPEC {}
#[doc = "`reset()` method sets RD_SYS_PART1_DATA1 to value 0"]
impl crate::Resettable for RD_SYS_PART1_DATA1_SPEC {}
