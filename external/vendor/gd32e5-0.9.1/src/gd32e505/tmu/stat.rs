#[doc = "Register `STAT` reader"]
pub type R = crate::R<StatSpec>;
#[doc = "Field `OVRF` reader - The flag of overflow"]
pub type OvrfR = crate::BitReader;
#[doc = "Field `UDRF` reader - The flag of underflow"]
pub type UdrfR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The flag of overflow"]
    #[inline(always)]
    pub fn ovrf(&self) -> OvrfR {
        OvrfR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The flag of underflow"]
    #[inline(always)]
    pub fn udrf(&self) -> UdrfR {
        UdrfR::new(((self.bits >> 1) & 1) != 0)
    }
}
#[doc = "Status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct StatSpec;
impl crate::RegisterSpec for StatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`stat::R`](R) reader structure"]
impl crate::Readable for StatSpec {}
#[doc = "`reset()` method sets STAT to value 0"]
impl crate::Resettable for StatSpec {
    const RESET_VALUE: u32 = 0;
}
