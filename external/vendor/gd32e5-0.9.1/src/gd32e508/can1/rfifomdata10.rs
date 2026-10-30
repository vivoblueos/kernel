#[doc = "Register `RFIFOMDATA10` reader"]
pub type R = crate::R<Rfifomdata10Spec>;
#[doc = "Field `DB4` reader - Data byte 4"]
pub type Db4R = crate::FieldReader;
#[doc = "Field `DB5` reader - Data byte 5"]
pub type Db5R = crate::FieldReader;
#[doc = "Field `DB6` reader - Data byte 6"]
pub type Db6R = crate::FieldReader;
#[doc = "Field `DB7` reader - Data byte 7"]
pub type Db7R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:7 - Data byte 4"]
    #[inline(always)]
    pub fn db4(&self) -> Db4R {
        Db4R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - Data byte 5"]
    #[inline(always)]
    pub fn db5(&self) -> Db5R {
        Db5R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - Data byte 6"]
    #[inline(always)]
    pub fn db6(&self) -> Db6R {
        Db6R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - Data byte 7"]
    #[inline(always)]
    pub fn db7(&self) -> Db7R {
        Db7R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[doc = "Receive FIFO0 mailbox data1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifomdata10::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Rfifomdata10Spec;
impl crate::RegisterSpec for Rfifomdata10Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rfifomdata10::R`](R) reader structure"]
impl crate::Readable for Rfifomdata10Spec {}
#[doc = "`reset()` method sets RFIFOMDATA10 to value 0"]
impl crate::Resettable for Rfifomdata10Spec {
    const RESET_VALUE: u32 = 0;
}
