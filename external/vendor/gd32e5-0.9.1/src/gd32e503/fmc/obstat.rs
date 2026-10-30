#[doc = "Register `OBSTAT` reader"]
pub type R = crate::R<ObstatSpec>;
#[doc = "Field `OBERR` reader - Option bytes read error bit"]
pub type OberrR = crate::BitReader;
#[doc = "Field `SPC` reader - Option bytes security protection code"]
pub type SpcR = crate::BitReader;
#[doc = "Field `USER` reader - Store USER of option bytes block after system reset"]
pub type UserR = crate::FieldReader;
#[doc = "Field `DATA` reader - Store DATA\\[15:0\\]
of option bytes block after system reset"]
pub type DataR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bit 0 - Option bytes read error bit"]
    #[inline(always)]
    pub fn oberr(&self) -> OberrR {
        OberrR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Option bytes security protection code"]
    #[inline(always)]
    pub fn spc(&self) -> SpcR {
        SpcR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:9 - Store USER of option bytes block after system reset"]
    #[inline(always)]
    pub fn user(&self) -> UserR {
        UserR::new(((self.bits >> 2) & 0xff) as u8)
    }
    #[doc = "Bits 10:25 - Store DATA\\[15:0\\]
of option bytes block after system reset"]
    #[inline(always)]
    pub fn data(&self) -> DataR {
        DataR::new(((self.bits >> 10) & 0xffff) as u16)
    }
}
#[doc = "Option byte status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`obstat::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ObstatSpec;
impl crate::RegisterSpec for ObstatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`obstat::R`](R) reader structure"]
impl crate::Readable for ObstatSpec {}
#[doc = "`reset()` method sets OBSTAT to value 0"]
impl crate::Resettable for ObstatSpec {
    const RESET_VALUE: u32 = 0;
}
