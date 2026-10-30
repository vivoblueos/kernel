#[doc = "Register `STAT` reader"]
pub type R = crate::R<StatSpec>;
#[doc = "Field `CKOKIF` reader - Clock trim OK interrupt flag"]
pub type CkokifR = crate::BitReader;
#[doc = "Field `CKWARNIF` reader - Clock trim warning interrupt flag"]
pub type CkwarnifR = crate::BitReader;
#[doc = "Field `ERRIF` reader - Error interrupt flag"]
pub type ErrifR = crate::BitReader;
#[doc = "Field `EREFIF` reader - Expect reference interrupt flag"]
pub type ErefifR = crate::BitReader;
#[doc = "Field `CKERR` reader - Clock trim error bit"]
pub type CkerrR = crate::BitReader;
#[doc = "Field `REFMISS` reader - Reference sync pulse miss"]
pub type RefmissR = crate::BitReader;
#[doc = "Field `TRIMERR` reader - Trim value error bit"]
pub type TrimerrR = crate::BitReader;
#[doc = "Field `REFDIR` reader - CTC trim counter direction when reference sync pulse"]
pub type RefdirR = crate::BitReader;
#[doc = "Field `REFCAP` reader - CTC counter capture when reference sync pulse"]
pub type RefcapR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bit 0 - Clock trim OK interrupt flag"]
    #[inline(always)]
    pub fn ckokif(&self) -> CkokifR {
        CkokifR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Clock trim warning interrupt flag"]
    #[inline(always)]
    pub fn ckwarnif(&self) -> CkwarnifR {
        CkwarnifR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Error interrupt flag"]
    #[inline(always)]
    pub fn errif(&self) -> ErrifR {
        ErrifR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Expect reference interrupt flag"]
    #[inline(always)]
    pub fn erefif(&self) -> ErefifR {
        ErefifR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 8 - Clock trim error bit"]
    #[inline(always)]
    pub fn ckerr(&self) -> CkerrR {
        CkerrR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Reference sync pulse miss"]
    #[inline(always)]
    pub fn refmiss(&self) -> RefmissR {
        RefmissR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Trim value error bit"]
    #[inline(always)]
    pub fn trimerr(&self) -> TrimerrR {
        TrimerrR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 15 - CTC trim counter direction when reference sync pulse"]
    #[inline(always)]
    pub fn refdir(&self) -> RefdirR {
        RefdirR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 16:31 - CTC counter capture when reference sync pulse"]
    #[inline(always)]
    pub fn refcap(&self) -> RefcapR {
        RefcapR::new(((self.bits >> 16) & 0xffff) as u16)
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
