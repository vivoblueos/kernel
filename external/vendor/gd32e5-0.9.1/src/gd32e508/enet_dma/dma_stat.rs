#[doc = "Register `DMA_STAT` reader"]
pub type R = crate::R<DmaStatSpec>;
#[doc = "Register `DMA_STAT` writer"]
pub type W = crate::W<DmaStatSpec>;
#[doc = "Field `TS` reader - Transmit status"]
pub type TsR = crate::BitReader;
#[doc = "Field `TS` writer - Transmit status"]
pub type TsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TPS` reader - Transmit process stopped status"]
pub type TpsR = crate::BitReader;
#[doc = "Field `TPS` writer - Transmit process stopped status"]
pub type TpsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TBU` reader - Transmit buffer unavailable status"]
pub type TbuR = crate::BitReader;
#[doc = "Field `TBU` writer - Transmit buffer unavailable status"]
pub type TbuW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TJT` reader - Transmit jabber timeout status"]
pub type TjtR = crate::BitReader;
#[doc = "Field `TJT` writer - Transmit jabber timeout status"]
pub type TjtW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RO` reader - Receive overflow status"]
pub type RoR = crate::BitReader;
#[doc = "Field `RO` writer - Receive overflow status"]
pub type RoW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TU` reader - Transmit underflow status"]
pub type TuR = crate::BitReader;
#[doc = "Field `TU` writer - Transmit underflow status"]
pub type TuW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RS` reader - Receive status"]
pub type RsR = crate::BitReader;
#[doc = "Field `RS` writer - Receive status"]
pub type RsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RBU` reader - Receive buffer unavailable status"]
pub type RbuR = crate::BitReader;
#[doc = "Field `RBU` writer - Receive buffer unavailable status"]
pub type RbuW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RPS` reader - Receive process stopped status"]
pub type RpsR = crate::BitReader;
#[doc = "Field `RPS` writer - Receive process stopped status"]
pub type RpsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RWT` reader - Receive watchdog timeout status"]
pub type RwtR = crate::BitReader;
#[doc = "Field `RWT` writer - Receive watchdog timeout status"]
pub type RwtW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ET` reader - Early transmit status"]
pub type EtR = crate::BitReader;
#[doc = "Field `ET` writer - Early transmit status"]
pub type EtW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FBE` reader - Fatal bus error status"]
pub type FbeR = crate::BitReader;
#[doc = "Field `FBE` writer - Fatal bus error status"]
pub type FbeW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ER` reader - Early receive status"]
pub type ErR = crate::BitReader;
#[doc = "Field `ER` writer - Early receive status"]
pub type ErW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AI` reader - Abnormal interrupt summary"]
pub type AiR = crate::BitReader;
#[doc = "Field `AI` writer - Abnormal interrupt summary"]
pub type AiW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NI` reader - Normal interrupt summary"]
pub type NiR = crate::BitReader;
#[doc = "Field `NI` writer - Normal interrupt summary"]
pub type NiW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RP` reader - Receive process state"]
pub type RpR = crate::FieldReader;
#[doc = "Field `TP` reader - Transmit process state"]
pub type TpR = crate::FieldReader;
#[doc = "Field `EB` reader - Error bits status"]
pub type EbR = crate::FieldReader;
#[doc = "Field `MSC` reader - MSC status"]
pub type MscR = crate::BitReader;
#[doc = "Field `WUM` reader - WUM status"]
pub type WumR = crate::BitReader;
#[doc = "Field `TST` reader - Time stamp trigger status"]
pub type TstR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Transmit status"]
    #[inline(always)]
    pub fn ts(&self) -> TsR {
        TsR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Transmit process stopped status"]
    #[inline(always)]
    pub fn tps(&self) -> TpsR {
        TpsR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Transmit buffer unavailable status"]
    #[inline(always)]
    pub fn tbu(&self) -> TbuR {
        TbuR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Transmit jabber timeout status"]
    #[inline(always)]
    pub fn tjt(&self) -> TjtR {
        TjtR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Receive overflow status"]
    #[inline(always)]
    pub fn ro(&self) -> RoR {
        RoR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Transmit underflow status"]
    #[inline(always)]
    pub fn tu(&self) -> TuR {
        TuR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Receive status"]
    #[inline(always)]
    pub fn rs(&self) -> RsR {
        RsR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Receive buffer unavailable status"]
    #[inline(always)]
    pub fn rbu(&self) -> RbuR {
        RbuR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Receive process stopped status"]
    #[inline(always)]
    pub fn rps(&self) -> RpsR {
        RpsR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Receive watchdog timeout status"]
    #[inline(always)]
    pub fn rwt(&self) -> RwtR {
        RwtR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Early transmit status"]
    #[inline(always)]
    pub fn et(&self) -> EtR {
        EtR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 13 - Fatal bus error status"]
    #[inline(always)]
    pub fn fbe(&self) -> FbeR {
        FbeR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Early receive status"]
    #[inline(always)]
    pub fn er(&self) -> ErR {
        ErR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Abnormal interrupt summary"]
    #[inline(always)]
    pub fn ai(&self) -> AiR {
        AiR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Normal interrupt summary"]
    #[inline(always)]
    pub fn ni(&self) -> NiR {
        NiR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bits 17:19 - Receive process state"]
    #[inline(always)]
    pub fn rp(&self) -> RpR {
        RpR::new(((self.bits >> 17) & 7) as u8)
    }
    #[doc = "Bits 20:22 - Transmit process state"]
    #[inline(always)]
    pub fn tp(&self) -> TpR {
        TpR::new(((self.bits >> 20) & 7) as u8)
    }
    #[doc = "Bits 23:25 - Error bits status"]
    #[inline(always)]
    pub fn eb(&self) -> EbR {
        EbR::new(((self.bits >> 23) & 7) as u8)
    }
    #[doc = "Bit 27 - MSC status"]
    #[inline(always)]
    pub fn msc(&self) -> MscR {
        MscR::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - WUM status"]
    #[inline(always)]
    pub fn wum(&self) -> WumR {
        WumR::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - Time stamp trigger status"]
    #[inline(always)]
    pub fn tst(&self) -> TstR {
        TstR::new(((self.bits >> 29) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Transmit status"]
    #[inline(always)]
    #[must_use]
    pub fn ts(&mut self) -> TsW<DmaStatSpec> {
        TsW::new(self, 0)
    }
    #[doc = "Bit 1 - Transmit process stopped status"]
    #[inline(always)]
    #[must_use]
    pub fn tps(&mut self) -> TpsW<DmaStatSpec> {
        TpsW::new(self, 1)
    }
    #[doc = "Bit 2 - Transmit buffer unavailable status"]
    #[inline(always)]
    #[must_use]
    pub fn tbu(&mut self) -> TbuW<DmaStatSpec> {
        TbuW::new(self, 2)
    }
    #[doc = "Bit 3 - Transmit jabber timeout status"]
    #[inline(always)]
    #[must_use]
    pub fn tjt(&mut self) -> TjtW<DmaStatSpec> {
        TjtW::new(self, 3)
    }
    #[doc = "Bit 4 - Receive overflow status"]
    #[inline(always)]
    #[must_use]
    pub fn ro(&mut self) -> RoW<DmaStatSpec> {
        RoW::new(self, 4)
    }
    #[doc = "Bit 5 - Transmit underflow status"]
    #[inline(always)]
    #[must_use]
    pub fn tu(&mut self) -> TuW<DmaStatSpec> {
        TuW::new(self, 5)
    }
    #[doc = "Bit 6 - Receive status"]
    #[inline(always)]
    #[must_use]
    pub fn rs(&mut self) -> RsW<DmaStatSpec> {
        RsW::new(self, 6)
    }
    #[doc = "Bit 7 - Receive buffer unavailable status"]
    #[inline(always)]
    #[must_use]
    pub fn rbu(&mut self) -> RbuW<DmaStatSpec> {
        RbuW::new(self, 7)
    }
    #[doc = "Bit 8 - Receive process stopped status"]
    #[inline(always)]
    #[must_use]
    pub fn rps(&mut self) -> RpsW<DmaStatSpec> {
        RpsW::new(self, 8)
    }
    #[doc = "Bit 9 - Receive watchdog timeout status"]
    #[inline(always)]
    #[must_use]
    pub fn rwt(&mut self) -> RwtW<DmaStatSpec> {
        RwtW::new(self, 9)
    }
    #[doc = "Bit 10 - Early transmit status"]
    #[inline(always)]
    #[must_use]
    pub fn et(&mut self) -> EtW<DmaStatSpec> {
        EtW::new(self, 10)
    }
    #[doc = "Bit 13 - Fatal bus error status"]
    #[inline(always)]
    #[must_use]
    pub fn fbe(&mut self) -> FbeW<DmaStatSpec> {
        FbeW::new(self, 13)
    }
    #[doc = "Bit 14 - Early receive status"]
    #[inline(always)]
    #[must_use]
    pub fn er(&mut self) -> ErW<DmaStatSpec> {
        ErW::new(self, 14)
    }
    #[doc = "Bit 15 - Abnormal interrupt summary"]
    #[inline(always)]
    #[must_use]
    pub fn ai(&mut self) -> AiW<DmaStatSpec> {
        AiW::new(self, 15)
    }
    #[doc = "Bit 16 - Normal interrupt summary"]
    #[inline(always)]
    #[must_use]
    pub fn ni(&mut self) -> NiW<DmaStatSpec> {
        NiW::new(self, 16)
    }
}
#[doc = "Ethernet DMA status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_stat::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_stat::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DmaStatSpec;
impl crate::RegisterSpec for DmaStatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_stat::R`](R) reader structure"]
impl crate::Readable for DmaStatSpec {}
#[doc = "`write(|w| ..)` method takes [`dma_stat::W`](W) writer structure"]
impl crate::Writable for DmaStatSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DMA_STAT to value 0"]
impl crate::Resettable for DmaStatSpec {
    const RESET_VALUE: u32 = 0;
}
