#[doc = "Register `HPTFQSTAT` reader"]
pub type R = crate::R<HptfqstatSpec>;
#[doc = "Field `PTXFS` reader - Periodic transmit data FIFO space available"]
pub type PtxfsR = crate::FieldReader<u16>;
#[doc = "Field `PTXREQS` reader - Periodic transmit request queue space available"]
pub type PtxreqsR = crate::FieldReader;
#[doc = "Field `PTXREQT` reader - Top of the periodic transmit request queue"]
pub type PtxreqtR = crate::FieldReader;
impl R {
    #[doc = "Bits 0:15 - Periodic transmit data FIFO space available"]
    #[inline(always)]
    pub fn ptxfs(&self) -> PtxfsR {
        PtxfsR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:23 - Periodic transmit request queue space available"]
    #[inline(always)]
    pub fn ptxreqs(&self) -> PtxreqsR {
        PtxreqsR::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - Top of the periodic transmit request queue"]
    #[inline(always)]
    pub fn ptxreqt(&self) -> PtxreqtR {
        PtxreqtR::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[doc = "Host periodic transmit FIFO/queue status register (HPTFQSTAT)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hptfqstat::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HptfqstatSpec;
impl crate::RegisterSpec for HptfqstatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hptfqstat::R`](R) reader structure"]
impl crate::Readable for HptfqstatSpec {}
#[doc = "`reset()` method sets HPTFQSTAT to value 0x0008_0200"]
impl crate::Resettable for HptfqstatSpec {
    const RESET_VALUE: u32 = 0x0008_0200;
}
