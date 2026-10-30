#[doc = "Register `MAC_FCTL` reader"]
pub type R = crate::R<MacFctlSpec>;
#[doc = "Register `MAC_FCTL` writer"]
pub type W = crate::W<MacFctlSpec>;
#[doc = "Field `FLCB_BKPA` reader - Flow control busy/back pressure activate"]
pub type FlcbBkpaR = crate::BitReader;
#[doc = "Field `FLCB_BKPA` writer - Flow control busy/back pressure activate"]
pub type FlcbBkpaW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TFCEN` reader - Transmit flow control enable"]
pub type TfcenR = crate::BitReader;
#[doc = "Field `TFCEN` writer - Transmit flow control enable"]
pub type TfcenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFCEN` reader - Receive flow control enable"]
pub type RfcenR = crate::BitReader;
#[doc = "Field `RFCEN` writer - Receive flow control enable"]
pub type RfcenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UPFDT` reader - Unicast pause frame detect"]
pub type UpfdtR = crate::BitReader;
#[doc = "Field `UPFDT` writer - Unicast pause frame detect"]
pub type UpfdtW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLTS` reader - Pause low threshold"]
pub type PltsR = crate::FieldReader;
#[doc = "Field `PLTS` writer - Pause low threshold"]
pub type PltsW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `DZQP` reader - Disable Zero-quanta pause"]
pub type DzqpR = crate::BitReader;
#[doc = "Field `DZQP` writer - Disable Zero-quanta pause"]
pub type DzqpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PTM` reader - Pause time"]
pub type PtmR = crate::FieldReader<u16>;
#[doc = "Field `PTM` writer - Pause time"]
pub type PtmW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bit 0 - Flow control busy/back pressure activate"]
    #[inline(always)]
    pub fn flcb_bkpa(&self) -> FlcbBkpaR {
        FlcbBkpaR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Transmit flow control enable"]
    #[inline(always)]
    pub fn tfcen(&self) -> TfcenR {
        TfcenR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Receive flow control enable"]
    #[inline(always)]
    pub fn rfcen(&self) -> RfcenR {
        RfcenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Unicast pause frame detect"]
    #[inline(always)]
    pub fn upfdt(&self) -> UpfdtR {
        UpfdtR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:5 - Pause low threshold"]
    #[inline(always)]
    pub fn plts(&self) -> PltsR {
        PltsR::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bit 7 - Disable Zero-quanta pause"]
    #[inline(always)]
    pub fn dzqp(&self) -> DzqpR {
        DzqpR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 16:31 - Pause time"]
    #[inline(always)]
    pub fn ptm(&self) -> PtmR {
        PtmR::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bit 0 - Flow control busy/back pressure activate"]
    #[inline(always)]
    #[must_use]
    pub fn flcb_bkpa(&mut self) -> FlcbBkpaW<MacFctlSpec> {
        FlcbBkpaW::new(self, 0)
    }
    #[doc = "Bit 1 - Transmit flow control enable"]
    #[inline(always)]
    #[must_use]
    pub fn tfcen(&mut self) -> TfcenW<MacFctlSpec> {
        TfcenW::new(self, 1)
    }
    #[doc = "Bit 2 - Receive flow control enable"]
    #[inline(always)]
    #[must_use]
    pub fn rfcen(&mut self) -> RfcenW<MacFctlSpec> {
        RfcenW::new(self, 2)
    }
    #[doc = "Bit 3 - Unicast pause frame detect"]
    #[inline(always)]
    #[must_use]
    pub fn upfdt(&mut self) -> UpfdtW<MacFctlSpec> {
        UpfdtW::new(self, 3)
    }
    #[doc = "Bits 4:5 - Pause low threshold"]
    #[inline(always)]
    #[must_use]
    pub fn plts(&mut self) -> PltsW<MacFctlSpec> {
        PltsW::new(self, 4)
    }
    #[doc = "Bit 7 - Disable Zero-quanta pause"]
    #[inline(always)]
    #[must_use]
    pub fn dzqp(&mut self) -> DzqpW<MacFctlSpec> {
        DzqpW::new(self, 7)
    }
    #[doc = "Bits 16:31 - Pause time"]
    #[inline(always)]
    #[must_use]
    pub fn ptm(&mut self) -> PtmW<MacFctlSpec> {
        PtmW::new(self, 16)
    }
}
#[doc = "Ethernet MAC flow control register (MAC_FCTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_fctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_fctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacFctlSpec;
impl crate::RegisterSpec for MacFctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_fctl::R`](R) reader structure"]
impl crate::Readable for MacFctlSpec {}
#[doc = "`write(|w| ..)` method takes [`mac_fctl::W`](W) writer structure"]
impl crate::Writable for MacFctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MAC_FCTL to value 0"]
impl crate::Resettable for MacFctlSpec {
    const RESET_VALUE: u32 = 0;
}
