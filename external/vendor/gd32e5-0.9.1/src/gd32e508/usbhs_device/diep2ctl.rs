#[doc = "Register `DIEP2CTL` reader"]
pub type R = crate::R<Diep2ctlSpec>;
#[doc = "Register `DIEP2CTL` writer"]
pub type W = crate::W<Diep2ctlSpec>;
#[doc = "Field `MPL` reader - maximum packet length"]
pub type MplR = crate::FieldReader<u16>;
#[doc = "Field `MPL` writer - maximum packet length"]
pub type MplW<'a, REG> = crate::FieldWriter<'a, REG, 11, u16>;
#[doc = "Field `EPACT` reader - Endpoint active"]
pub type EpactR = crate::BitReader;
#[doc = "Field `EPACT` writer - Endpoint active"]
pub type EpactW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EOFRM_DPID` reader - EOFRM/DPID"]
pub type EofrmDpidR = crate::BitReader;
#[doc = "Field `NAKS` reader - NAK status"]
pub type NaksR = crate::BitReader;
#[doc = "Field `EPTYPE` reader - Endpoint type"]
pub type EptypeR = crate::FieldReader;
#[doc = "Field `EPTYPE` writer - Endpoint type"]
pub type EptypeW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `STALL` reader - STALL handshake"]
pub type StallR = crate::BitReader;
#[doc = "Field `STALL` writer - STALL handshake"]
pub type StallW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TXFNUM` reader - Tx FIFO number"]
pub type TxfnumR = crate::FieldReader;
#[doc = "Field `TXFNUM` writer - Tx FIFO number"]
pub type TxfnumW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CNAK` writer - Clear NAK"]
pub type CnakW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SNAK` writer - Set NAK"]
pub type SnakW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SD0PID_SEVENFRM` writer - SD0PID/SEVNFRM"]
pub type Sd0pidSevenfrmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SD1PID_SODDFRM` writer - Set DATA1 PID/Set odd frame"]
pub type Sd1pidSoddfrmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EPD` reader - Endpoint disable"]
pub type EpdR = crate::BitReader;
#[doc = "Field `EPD` writer - Endpoint disable"]
pub type EpdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EPEN` reader - Endpoint enable"]
pub type EpenR = crate::BitReader;
#[doc = "Field `EPEN` writer - Endpoint enable"]
pub type EpenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:10 - maximum packet length"]
    #[inline(always)]
    pub fn mpl(&self) -> MplR {
        MplR::new((self.bits & 0x07ff) as u16)
    }
    #[doc = "Bit 15 - Endpoint active"]
    #[inline(always)]
    pub fn epact(&self) -> EpactR {
        EpactR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - EOFRM/DPID"]
    #[inline(always)]
    pub fn eofrm_dpid(&self) -> EofrmDpidR {
        EofrmDpidR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - NAK status"]
    #[inline(always)]
    pub fn naks(&self) -> NaksR {
        NaksR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bits 18:19 - Endpoint type"]
    #[inline(always)]
    pub fn eptype(&self) -> EptypeR {
        EptypeR::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bit 21 - STALL handshake"]
    #[inline(always)]
    pub fn stall(&self) -> StallR {
        StallR::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bits 22:25 - Tx FIFO number"]
    #[inline(always)]
    pub fn txfnum(&self) -> TxfnumR {
        TxfnumR::new(((self.bits >> 22) & 0x0f) as u8)
    }
    #[doc = "Bit 30 - Endpoint disable"]
    #[inline(always)]
    pub fn epd(&self) -> EpdR {
        EpdR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Endpoint enable"]
    #[inline(always)]
    pub fn epen(&self) -> EpenR {
        EpenR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:10 - maximum packet length"]
    #[inline(always)]
    #[must_use]
    pub fn mpl(&mut self) -> MplW<Diep2ctlSpec> {
        MplW::new(self, 0)
    }
    #[doc = "Bit 15 - Endpoint active"]
    #[inline(always)]
    #[must_use]
    pub fn epact(&mut self) -> EpactW<Diep2ctlSpec> {
        EpactW::new(self, 15)
    }
    #[doc = "Bits 18:19 - Endpoint type"]
    #[inline(always)]
    #[must_use]
    pub fn eptype(&mut self) -> EptypeW<Diep2ctlSpec> {
        EptypeW::new(self, 18)
    }
    #[doc = "Bit 21 - STALL handshake"]
    #[inline(always)]
    #[must_use]
    pub fn stall(&mut self) -> StallW<Diep2ctlSpec> {
        StallW::new(self, 21)
    }
    #[doc = "Bits 22:25 - Tx FIFO number"]
    #[inline(always)]
    #[must_use]
    pub fn txfnum(&mut self) -> TxfnumW<Diep2ctlSpec> {
        TxfnumW::new(self, 22)
    }
    #[doc = "Bit 26 - Clear NAK"]
    #[inline(always)]
    #[must_use]
    pub fn cnak(&mut self) -> CnakW<Diep2ctlSpec> {
        CnakW::new(self, 26)
    }
    #[doc = "Bit 27 - Set NAK"]
    #[inline(always)]
    #[must_use]
    pub fn snak(&mut self) -> SnakW<Diep2ctlSpec> {
        SnakW::new(self, 27)
    }
    #[doc = "Bit 28 - SD0PID/SEVNFRM"]
    #[inline(always)]
    #[must_use]
    pub fn sd0pid_sevenfrm(&mut self) -> Sd0pidSevenfrmW<Diep2ctlSpec> {
        Sd0pidSevenfrmW::new(self, 28)
    }
    #[doc = "Bit 29 - Set DATA1 PID/Set odd frame"]
    #[inline(always)]
    #[must_use]
    pub fn sd1pid_soddfrm(&mut self) -> Sd1pidSoddfrmW<Diep2ctlSpec> {
        Sd1pidSoddfrmW::new(self, 29)
    }
    #[doc = "Bit 30 - Endpoint disable"]
    #[inline(always)]
    #[must_use]
    pub fn epd(&mut self) -> EpdW<Diep2ctlSpec> {
        EpdW::new(self, 30)
    }
    #[doc = "Bit 31 - Endpoint enable"]
    #[inline(always)]
    #[must_use]
    pub fn epen(&mut self) -> EpenW<Diep2ctlSpec> {
        EpenW::new(self, 31)
    }
}
#[doc = "device endpoint-2 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep2ctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep2ctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Diep2ctlSpec;
impl crate::RegisterSpec for Diep2ctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diep2ctl::R`](R) reader structure"]
impl crate::Readable for Diep2ctlSpec {}
#[doc = "`write(|w| ..)` method takes [`diep2ctl::W`](W) writer structure"]
impl crate::Writable for Diep2ctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DIEP2CTL to value 0"]
impl crate::Resettable for Diep2ctlSpec {
    const RESET_VALUE: u32 = 0;
}
