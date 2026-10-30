#[doc = "Register `RFIFOMI1` reader"]
pub type R = crate::R<Rfifomi1Spec>;
#[doc = "Field `FT` reader - Frame type"]
pub type FtR = crate::BitReader;
#[doc = "Field `FF` reader - Frame format"]
pub type FfR = crate::BitReader;
#[doc = "Field `EFID` reader - The frame identifier"]
pub type EfidR = crate::FieldReader<u32>;
#[doc = "Field `SFID_EFID` reader - The frame identifier"]
pub type SfidEfidR = crate::FieldReader<u16>;
impl R {
    #[doc = "Bit 1 - Frame type"]
    #[inline(always)]
    pub fn ft(&self) -> FtR {
        FtR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Frame format"]
    #[inline(always)]
    pub fn ff(&self) -> FfR {
        FfR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bits 3:20 - The frame identifier"]
    #[inline(always)]
    pub fn efid(&self) -> EfidR {
        EfidR::new((self.bits >> 3) & 0x0003_ffff)
    }
    #[doc = "Bits 21:31 - The frame identifier"]
    #[inline(always)]
    pub fn sfid_efid(&self) -> SfidEfidR {
        SfidEfidR::new(((self.bits >> 21) & 0x07ff) as u16)
    }
}
#[doc = "Receive FIFO1 mailbox identifier register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifomi1::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Rfifomi1Spec;
impl crate::RegisterSpec for Rfifomi1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rfifomi1::R`](R) reader structure"]
impl crate::Readable for Rfifomi1Spec {}
#[doc = "`reset()` method sets RFIFOMI1 to value 0"]
impl crate::Resettable for Rfifomi1Spec {
    const RESET_VALUE: u32 = 0;
}
