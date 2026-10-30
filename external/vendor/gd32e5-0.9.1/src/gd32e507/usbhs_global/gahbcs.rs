#[doc = "Register `GAHBCS` reader"]
pub type R = crate::R<GahbcsSpec>;
#[doc = "Register `GAHBCS` writer"]
pub type W = crate::W<GahbcsSpec>;
#[doc = "Field `GINTEN` reader - Global interrupt enable"]
pub type GintenR = crate::BitReader;
#[doc = "Field `GINTEN` writer - Global interrupt enable"]
pub type GintenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BURST` reader - The AHB burst type used by DMA"]
pub type BurstR = crate::FieldReader;
#[doc = "Field `BURST` writer - The AHB burst type used by DMA"]
pub type BurstW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `DMAEN` reader - DMA function Enable"]
pub type DmaenR = crate::BitReader;
#[doc = "Field `DMAEN` writer - DMA function Enable"]
pub type DmaenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TXFTH` reader - Tx FIFO threshold"]
pub type TxfthR = crate::BitReader;
#[doc = "Field `TXFTH` writer - Tx FIFO threshold"]
pub type TxfthW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PTXFTH` reader - Periodic Tx FIFO threshold"]
pub type PtxfthR = crate::BitReader;
#[doc = "Field `PTXFTH` writer - Periodic Tx FIFO threshold"]
pub type PtxfthW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Global interrupt enable"]
    #[inline(always)]
    pub fn ginten(&self) -> GintenR {
        GintenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:4 - The AHB burst type used by DMA"]
    #[inline(always)]
    pub fn burst(&self) -> BurstR {
        BurstR::new(((self.bits >> 1) & 0x0f) as u8)
    }
    #[doc = "Bit 5 - DMA function Enable"]
    #[inline(always)]
    pub fn dmaen(&self) -> DmaenR {
        DmaenR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 7 - Tx FIFO threshold"]
    #[inline(always)]
    pub fn txfth(&self) -> TxfthR {
        TxfthR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Periodic Tx FIFO threshold"]
    #[inline(always)]
    pub fn ptxfth(&self) -> PtxfthR {
        PtxfthR::new(((self.bits >> 8) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Global interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn ginten(&mut self) -> GintenW<GahbcsSpec> {
        GintenW::new(self, 0)
    }
    #[doc = "Bits 1:4 - The AHB burst type used by DMA"]
    #[inline(always)]
    #[must_use]
    pub fn burst(&mut self) -> BurstW<GahbcsSpec> {
        BurstW::new(self, 1)
    }
    #[doc = "Bit 5 - DMA function Enable"]
    #[inline(always)]
    #[must_use]
    pub fn dmaen(&mut self) -> DmaenW<GahbcsSpec> {
        DmaenW::new(self, 5)
    }
    #[doc = "Bit 7 - Tx FIFO threshold"]
    #[inline(always)]
    #[must_use]
    pub fn txfth(&mut self) -> TxfthW<GahbcsSpec> {
        TxfthW::new(self, 7)
    }
    #[doc = "Bit 8 - Periodic Tx FIFO threshold"]
    #[inline(always)]
    #[must_use]
    pub fn ptxfth(&mut self) -> PtxfthW<GahbcsSpec> {
        PtxfthW::new(self, 8)
    }
}
#[doc = "Global AHB control and status register (USBHS_GAHBCS)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`gahbcs::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`gahbcs::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GahbcsSpec;
impl crate::RegisterSpec for GahbcsSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`gahbcs::R`](R) reader structure"]
impl crate::Readable for GahbcsSpec {}
#[doc = "`write(|w| ..)` method takes [`gahbcs::W`](W) writer structure"]
impl crate::Writable for GahbcsSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets GAHBCS to value 0"]
impl crate::Resettable for GahbcsSpec {
    const RESET_VALUE: u32 = 0;
}
