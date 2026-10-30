#[doc = "Register `RFIFOMDATA00` reader"]
pub type R = crate::R<Rfifomdata00Spec>;
#[doc = "Field `DB0` reader - Data byte 0"]
pub type Db0R = crate::FieldReader;
#[doc = "Field `DB1` reader - Data byte 1"]
pub type Db1R = crate::FieldReader;
#[doc = "Field `DB2` reader - Data byte 2"]
pub type Db2R = crate::FieldReader;
#[doc = "Field `DB3` reader - Data byte 3"]
pub type Db3R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:7 - Data byte 0"]
    #[inline(always)]
    pub fn db0(&self) -> Db0R {
        Db0R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - Data byte 1"]
    #[inline(always)]
    pub fn db1(&self) -> Db1R {
        Db1R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - Data byte 2"]
    #[inline(always)]
    pub fn db2(&self) -> Db2R {
        Db2R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - Data byte 3"]
    #[inline(always)]
    pub fn db3(&self) -> Db3R {
        Db3R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[doc = "Receive FIFO0 mailbox data0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifomdata00::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Rfifomdata00Spec;
impl crate::RegisterSpec for Rfifomdata00Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rfifomdata00::R`](R) reader structure"]
impl crate::Readable for Rfifomdata00Spec {}
#[doc = "`reset()` method sets RFIFOMDATA00 to value 0"]
impl crate::Resettable for Rfifomdata00Spec {
    const RESET_VALUE: u32 = 0;
}
