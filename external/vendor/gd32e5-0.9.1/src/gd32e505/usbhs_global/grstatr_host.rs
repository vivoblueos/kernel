#[doc = "Register `GRSTATR_Host` reader"]
pub type R = crate::R<GrstatrHostSpec>;
#[doc = "Field `CNUM` reader - Channel number"]
pub type CnumR = crate::FieldReader;
#[doc = "Field `BCOUNT` reader - Byte count"]
pub type BcountR = crate::FieldReader<u16>;
#[doc = "Field `DPID` reader - Data PID"]
pub type DpidR = crate::FieldReader;
#[doc = "Field `RPCKST` reader - Reivece packet status"]
pub type RpckstR = crate::FieldReader;
impl R {
    #[doc = "Bits 0:3 - Channel number"]
    #[inline(always)]
    pub fn cnum(&self) -> CnumR {
        CnumR::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:14 - Byte count"]
    #[inline(always)]
    pub fn bcount(&self) -> BcountR {
        BcountR::new(((self.bits >> 4) & 0x07ff) as u16)
    }
    #[doc = "Bits 15:16 - Data PID"]
    #[inline(always)]
    pub fn dpid(&self) -> DpidR {
        DpidR::new(((self.bits >> 15) & 3) as u8)
    }
    #[doc = "Bits 17:20 - Reivece packet status"]
    #[inline(always)]
    pub fn rpckst(&self) -> RpckstR {
        RpckstR::new(((self.bits >> 17) & 0x0f) as u8)
    }
}
#[doc = "Global Receive status read(Host mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`grstatr_host::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GrstatrHostSpec;
impl crate::RegisterSpec for GrstatrHostSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`grstatr_host::R`](R) reader structure"]
impl crate::Readable for GrstatrHostSpec {}
#[doc = "`reset()` method sets GRSTATR_Host to value 0"]
impl crate::Resettable for GrstatrHostSpec {
    const RESET_VALUE: u32 = 0;
}
