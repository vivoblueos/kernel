#[doc = "Register `HNPTFQSTAT` reader"]
pub type R = crate::R<HnptfqstatSpec>;
#[doc = "Field `NPTXFS` reader - Non-periodic TxFIFO space"]
pub type NptxfsR = crate::FieldReader<u16>;
#[doc = "Field `NPTXRQS` reader - Non-periodic transmit request queue space"]
pub type NptxrqsR = crate::FieldReader;
#[doc = "Field `NPTXRQTOP` reader - Top of the non-periodic transmit request queue"]
pub type NptxrqtopR = crate::FieldReader;
impl R {
    #[doc = "Bits 0:15 - Non-periodic TxFIFO space"]
    #[inline(always)]
    pub fn nptxfs(&self) -> NptxfsR {
        NptxfsR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:23 - Non-periodic transmit request queue space"]
    #[inline(always)]
    pub fn nptxrqs(&self) -> NptxrqsR {
        NptxrqsR::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:30 - Top of the non-periodic transmit request queue"]
    #[inline(always)]
    pub fn nptxrqtop(&self) -> NptxrqtopR {
        NptxrqtopR::new(((self.bits >> 24) & 0x7f) as u8)
    }
}
#[doc = "Host non-periodic transmit FIFO/queue status register (HNPTFQSTAT)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hnptfqstat::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HnptfqstatSpec;
impl crate::RegisterSpec for HnptfqstatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hnptfqstat::R`](R) reader structure"]
impl crate::Readable for HnptfqstatSpec {}
#[doc = "`reset()` method sets HNPTFQSTAT to value 0x0008_0200"]
impl crate::Resettable for HnptfqstatSpec {
    const RESET_VALUE: u32 = 0x0008_0200;
}
