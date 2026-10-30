#[doc = "Register `EP2CS` reader"]
pub type R = crate::R<Ep2csSpec>;
#[doc = "Register `EP2CS` writer"]
pub type W = crate::W<Ep2csSpec>;
#[doc = "Field `EP_AR` reader - Endpoint address"]
pub type EpArR = crate::FieldReader;
#[doc = "Field `EP_AR` writer - Endpoint address"]
pub type EpArW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `TX_STA` reader - Status bits, for transmission transfers"]
pub type TxStaR = crate::FieldReader;
#[doc = "Field `TX_STA` writer - Status bits, for transmission transfers"]
pub type TxStaW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `TX_DTG` reader - Data Toggle, for transmission transfers"]
pub type TxDtgR = crate::BitReader;
#[doc = "Field `TX_DTG` writer - Data Toggle, for transmission transfers"]
pub type TxDtgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_ST` reader - Correct Transfer for transmission"]
pub type TxStR = crate::BitReader;
#[doc = "Field `TX_ST` writer - Correct Transfer for transmission"]
pub type TxStW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EP_KCTL` reader - Endpoint kind"]
pub type EpKctlR = crate::BitReader;
#[doc = "Field `EP_KCTL` writer - Endpoint kind"]
pub type EpKctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EP_CTL` reader - Endpoint type"]
pub type EpCtlR = crate::FieldReader;
#[doc = "Field `EP_CTL` writer - Endpoint type"]
pub type EpCtlW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SETUP` reader - Setup transaction completed"]
pub type SetupR = crate::BitReader;
#[doc = "Field `SETUP` writer - Setup transaction completed"]
pub type SetupW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_STA` reader - Status bits, for reception transfers"]
pub type RxStaR = crate::FieldReader;
#[doc = "Field `RX_STA` writer - Status bits, for reception transfers"]
pub type RxStaW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `RX_DTG` reader - Data Toggle, for reception transfers"]
pub type RxDtgR = crate::BitReader;
#[doc = "Field `RX_DTG` writer - Data Toggle, for reception transfers"]
pub type RxDtgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_ST` reader - Correct transfer for reception"]
pub type RxStR = crate::BitReader;
#[doc = "Field `RX_ST` writer - Correct transfer for reception"]
pub type RxStW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:3 - Endpoint address"]
    #[inline(always)]
    pub fn ep_ar(&self) -> EpArR {
        EpArR::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:5 - Status bits, for transmission transfers"]
    #[inline(always)]
    pub fn tx_sta(&self) -> TxStaR {
        TxStaR::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bit 6 - Data Toggle, for transmission transfers"]
    #[inline(always)]
    pub fn tx_dtg(&self) -> TxDtgR {
        TxDtgR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Correct Transfer for transmission"]
    #[inline(always)]
    pub fn tx_st(&self) -> TxStR {
        TxStR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Endpoint kind"]
    #[inline(always)]
    pub fn ep_kctl(&self) -> EpKctlR {
        EpKctlR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bits 9:10 - Endpoint type"]
    #[inline(always)]
    pub fn ep_ctl(&self) -> EpCtlR {
        EpCtlR::new(((self.bits >> 9) & 3) as u8)
    }
    #[doc = "Bit 11 - Setup transaction completed"]
    #[inline(always)]
    pub fn setup(&self) -> SetupR {
        SetupR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bits 12:13 - Status bits, for reception transfers"]
    #[inline(always)]
    pub fn rx_sta(&self) -> RxStaR {
        RxStaR::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bit 14 - Data Toggle, for reception transfers"]
    #[inline(always)]
    pub fn rx_dtg(&self) -> RxDtgR {
        RxDtgR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Correct transfer for reception"]
    #[inline(always)]
    pub fn rx_st(&self) -> RxStR {
        RxStR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:3 - Endpoint address"]
    #[inline(always)]
    #[must_use]
    pub fn ep_ar(&mut self) -> EpArW<Ep2csSpec> {
        EpArW::new(self, 0)
    }
    #[doc = "Bits 4:5 - Status bits, for transmission transfers"]
    #[inline(always)]
    #[must_use]
    pub fn tx_sta(&mut self) -> TxStaW<Ep2csSpec> {
        TxStaW::new(self, 4)
    }
    #[doc = "Bit 6 - Data Toggle, for transmission transfers"]
    #[inline(always)]
    #[must_use]
    pub fn tx_dtg(&mut self) -> TxDtgW<Ep2csSpec> {
        TxDtgW::new(self, 6)
    }
    #[doc = "Bit 7 - Correct Transfer for transmission"]
    #[inline(always)]
    #[must_use]
    pub fn tx_st(&mut self) -> TxStW<Ep2csSpec> {
        TxStW::new(self, 7)
    }
    #[doc = "Bit 8 - Endpoint kind"]
    #[inline(always)]
    #[must_use]
    pub fn ep_kctl(&mut self) -> EpKctlW<Ep2csSpec> {
        EpKctlW::new(self, 8)
    }
    #[doc = "Bits 9:10 - Endpoint type"]
    #[inline(always)]
    #[must_use]
    pub fn ep_ctl(&mut self) -> EpCtlW<Ep2csSpec> {
        EpCtlW::new(self, 9)
    }
    #[doc = "Bit 11 - Setup transaction completed"]
    #[inline(always)]
    #[must_use]
    pub fn setup(&mut self) -> SetupW<Ep2csSpec> {
        SetupW::new(self, 11)
    }
    #[doc = "Bits 12:13 - Status bits, for reception transfers"]
    #[inline(always)]
    #[must_use]
    pub fn rx_sta(&mut self) -> RxStaW<Ep2csSpec> {
        RxStaW::new(self, 12)
    }
    #[doc = "Bit 14 - Data Toggle, for reception transfers"]
    #[inline(always)]
    #[must_use]
    pub fn rx_dtg(&mut self) -> RxDtgW<Ep2csSpec> {
        RxDtgW::new(self, 14)
    }
    #[doc = "Bit 15 - Correct transfer for reception"]
    #[inline(always)]
    #[must_use]
    pub fn rx_st(&mut self) -> RxStW<Ep2csSpec> {
        RxStW::new(self, 15)
    }
}
#[doc = "endpoint 2 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ep2cs::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ep2cs::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ep2csSpec;
impl crate::RegisterSpec for Ep2csSpec {
    type Ux = u16;
}
#[doc = "`read()` method returns [`ep2cs::R`](R) reader structure"]
impl crate::Readable for Ep2csSpec {}
#[doc = "`write(|w| ..)` method takes [`ep2cs::W`](W) writer structure"]
impl crate::Writable for Ep2csSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u16 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u16 = 0;
}
#[doc = "`reset()` method sets EP2CS to value 0"]
impl crate::Resettable for Ep2csSpec {
    const RESET_VALUE: u16 = 0;
}
