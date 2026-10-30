#[doc = "Register `RCRC` reader"]
pub type R = crate::R<RcrcSpec>;
#[doc = "Field `RCRC` reader - RX CRC register"]
pub type RcrcR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - RX CRC register"]
    #[inline(always)]
    pub fn rcrc(&self) -> RcrcR {
        RcrcR::new((self.bits & 0xffff) as u16)
    }
}
#[doc = "RX CRC register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rcrc::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RcrcSpec;
impl crate::RegisterSpec for RcrcSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rcrc::R`](R) reader structure"]
impl crate::Readable for RcrcSpec {}
#[doc = "`reset()` method sets RCRC to value 0"]
impl crate::Resettable for RcrcSpec {
    const RESET_VALUE: u32 = 0;
}
