#[doc = "Register `DMA_BCTL` reader"]
pub type R = crate::R<DmaBctlSpec>;
#[doc = "Register `DMA_BCTL` writer"]
pub type W = crate::W<DmaBctlSpec>;
#[doc = "Field `SWR` reader - Software reset"]
pub type SwrR = crate::BitReader;
#[doc = "Field `SWR` writer - Software reset"]
pub type SwrW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DAB` reader - DMA Arbitration"]
pub type DabR = crate::BitReader;
#[doc = "Field `DAB` writer - DMA Arbitration"]
pub type DabW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DPSL` reader - Descriptor skip length"]
pub type DpslR = crate::FieldReader;
#[doc = "Field `DPSL` writer - Descriptor skip length"]
pub type DpslW<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `DFM` reader - Descriptor format mode"]
pub type DfmR = crate::BitReader;
#[doc = "Field `DFM` writer - Descriptor format mode"]
pub type DfmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PGBL` reader - Programmable burst length"]
pub type PgblR = crate::FieldReader;
#[doc = "Field `PGBL` writer - Programmable burst length"]
pub type PgblW<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `RTPR` reader - RxDMA and TxDMA transfer priority ratio"]
pub type RtprR = crate::FieldReader;
#[doc = "Field `RTPR` writer - RxDMA and TxDMA transfer priority ratio"]
pub type RtprW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `FB` reader - Fixed burst"]
pub type FbR = crate::BitReader;
#[doc = "Field `FB` writer - Fixed burst"]
pub type FbW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXDP` reader - Rx DMA PGBL"]
pub type RxdpR = crate::FieldReader;
#[doc = "Field `RXDP` writer - Rx DMA PGBL"]
pub type RxdpW<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `UIP` reader - Use independent PGBL"]
pub type UipR = crate::BitReader;
#[doc = "Field `UIP` writer - Use independent PGBL"]
pub type UipW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FPBL` reader - Four times PGBL mode"]
pub type FpblR = crate::BitReader;
#[doc = "Field `FPBL` writer - Four times PGBL mode"]
pub type FpblW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AA` reader - Address-aligned"]
pub type AaR = crate::BitReader;
#[doc = "Field `AA` writer - Address-aligned"]
pub type AaW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MB` reader - Mixed burst"]
pub type MbR = crate::BitReader;
#[doc = "Field `MB` writer - Mixed burst"]
pub type MbW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Software reset"]
    #[inline(always)]
    pub fn swr(&self) -> SwrR {
        SwrR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - DMA Arbitration"]
    #[inline(always)]
    pub fn dab(&self) -> DabR {
        DabR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:6 - Descriptor skip length"]
    #[inline(always)]
    pub fn dpsl(&self) -> DpslR {
        DpslR::new(((self.bits >> 2) & 0x1f) as u8)
    }
    #[doc = "Bit 7 - Descriptor format mode"]
    #[inline(always)]
    pub fn dfm(&self) -> DfmR {
        DfmR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:13 - Programmable burst length"]
    #[inline(always)]
    pub fn pgbl(&self) -> PgblR {
        PgblR::new(((self.bits >> 8) & 0x3f) as u8)
    }
    #[doc = "Bits 14:15 - RxDMA and TxDMA transfer priority ratio"]
    #[inline(always)]
    pub fn rtpr(&self) -> RtprR {
        RtprR::new(((self.bits >> 14) & 3) as u8)
    }
    #[doc = "Bit 16 - Fixed burst"]
    #[inline(always)]
    pub fn fb(&self) -> FbR {
        FbR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bits 17:22 - Rx DMA PGBL"]
    #[inline(always)]
    pub fn rxdp(&self) -> RxdpR {
        RxdpR::new(((self.bits >> 17) & 0x3f) as u8)
    }
    #[doc = "Bit 23 - Use independent PGBL"]
    #[inline(always)]
    pub fn uip(&self) -> UipR {
        UipR::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - Four times PGBL mode"]
    #[inline(always)]
    pub fn fpbl(&self) -> FpblR {
        FpblR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Address-aligned"]
    #[inline(always)]
    pub fn aa(&self) -> AaR {
        AaR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Mixed burst"]
    #[inline(always)]
    pub fn mb(&self) -> MbR {
        MbR::new(((self.bits >> 26) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Software reset"]
    #[inline(always)]
    #[must_use]
    pub fn swr(&mut self) -> SwrW<DmaBctlSpec> {
        SwrW::new(self, 0)
    }
    #[doc = "Bit 1 - DMA Arbitration"]
    #[inline(always)]
    #[must_use]
    pub fn dab(&mut self) -> DabW<DmaBctlSpec> {
        DabW::new(self, 1)
    }
    #[doc = "Bits 2:6 - Descriptor skip length"]
    #[inline(always)]
    #[must_use]
    pub fn dpsl(&mut self) -> DpslW<DmaBctlSpec> {
        DpslW::new(self, 2)
    }
    #[doc = "Bit 7 - Descriptor format mode"]
    #[inline(always)]
    #[must_use]
    pub fn dfm(&mut self) -> DfmW<DmaBctlSpec> {
        DfmW::new(self, 7)
    }
    #[doc = "Bits 8:13 - Programmable burst length"]
    #[inline(always)]
    #[must_use]
    pub fn pgbl(&mut self) -> PgblW<DmaBctlSpec> {
        PgblW::new(self, 8)
    }
    #[doc = "Bits 14:15 - RxDMA and TxDMA transfer priority ratio"]
    #[inline(always)]
    #[must_use]
    pub fn rtpr(&mut self) -> RtprW<DmaBctlSpec> {
        RtprW::new(self, 14)
    }
    #[doc = "Bit 16 - Fixed burst"]
    #[inline(always)]
    #[must_use]
    pub fn fb(&mut self) -> FbW<DmaBctlSpec> {
        FbW::new(self, 16)
    }
    #[doc = "Bits 17:22 - Rx DMA PGBL"]
    #[inline(always)]
    #[must_use]
    pub fn rxdp(&mut self) -> RxdpW<DmaBctlSpec> {
        RxdpW::new(self, 17)
    }
    #[doc = "Bit 23 - Use independent PGBL"]
    #[inline(always)]
    #[must_use]
    pub fn uip(&mut self) -> UipW<DmaBctlSpec> {
        UipW::new(self, 23)
    }
    #[doc = "Bit 24 - Four times PGBL mode"]
    #[inline(always)]
    #[must_use]
    pub fn fpbl(&mut self) -> FpblW<DmaBctlSpec> {
        FpblW::new(self, 24)
    }
    #[doc = "Bit 25 - Address-aligned"]
    #[inline(always)]
    #[must_use]
    pub fn aa(&mut self) -> AaW<DmaBctlSpec> {
        AaW::new(self, 25)
    }
    #[doc = "Bit 26 - Mixed burst"]
    #[inline(always)]
    #[must_use]
    pub fn mb(&mut self) -> MbW<DmaBctlSpec> {
        MbW::new(self, 26)
    }
}
#[doc = "Ethernet DMA bus control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_bctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_bctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DmaBctlSpec;
impl crate::RegisterSpec for DmaBctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_bctl::R`](R) reader structure"]
impl crate::Readable for DmaBctlSpec {}
#[doc = "`write(|w| ..)` method takes [`dma_bctl::W`](W) writer structure"]
impl crate::Writable for DmaBctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DMA_BCTL to value 0x0002_0101"]
impl crate::Resettable for DmaBctlSpec {
    const RESET_VALUE: u32 = 0x0002_0101;
}
