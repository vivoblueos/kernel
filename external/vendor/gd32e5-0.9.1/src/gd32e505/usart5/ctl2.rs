#[doc = "Register `CTL2` reader"]
pub type R = crate::R<Ctl2Spec>;
#[doc = "Register `CTL2` writer"]
pub type W = crate::W<Ctl2Spec>;
#[doc = "Field `ERRIE` reader - Error interrupt enable"]
pub type ErrieR = crate::BitReader;
#[doc = "Field `ERRIE` writer - Error interrupt enable"]
pub type ErrieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IREN` reader - IrDA mode enable"]
pub type IrenR = crate::BitReader;
#[doc = "Field `IREN` writer - IrDA mode enable"]
pub type IrenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IRLP` reader - IrDA low-power"]
pub type IrlpR = crate::BitReader;
#[doc = "Field `IRLP` writer - IrDA low-power"]
pub type IrlpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HDEN` reader - Half-duplex enable"]
pub type HdenR = crate::BitReader;
#[doc = "Field `HDEN` writer - Half-duplex enable"]
pub type HdenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NKEN` reader - NACK enable in Smartcard mode"]
pub type NkenR = crate::BitReader;
#[doc = "Field `NKEN` writer - NACK enable in Smartcard mode"]
pub type NkenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SCEN` reader - Smartcard mode enable"]
pub type ScenR = crate::BitReader;
#[doc = "Field `SCEN` writer - Smartcard mode enable"]
pub type ScenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DENR` reader - DMA enable for reception"]
pub type DenrR = crate::BitReader;
#[doc = "Field `DENR` writer - DMA enable for reception"]
pub type DenrW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DENT` reader - DMA enable for transmission"]
pub type DentR = crate::BitReader;
#[doc = "Field `DENT` writer - DMA enable for transmission"]
pub type DentW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OSB` reader - One sample bit method"]
pub type OsbR = crate::BitReader;
#[doc = "Field `OSB` writer - One sample bit method"]
pub type OsbW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OVRD` reader - Overrun disable"]
pub type OvrdR = crate::BitReader;
#[doc = "Field `OVRD` writer - Overrun disable"]
pub type OvrdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DDRE` reader - Disable DMA on reception error"]
pub type DdreR = crate::BitReader;
#[doc = "Field `DDRE` writer - Disable DMA on reception error"]
pub type DdreW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SCRTNUM` reader - Smartcard auto-retry number"]
pub type ScrtnumR = crate::FieldReader;
#[doc = "Field `SCRTNUM` writer - Smartcard auto-retry number"]
pub type ScrtnumW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `WUM` reader - Wakeup mode from Deep-sleep mode"]
pub type WumR = crate::FieldReader;
#[doc = "Field `WUM` writer - Wakeup mode from Deep-sleep mode"]
pub type WumW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `WUIE` reader - Wakeup from Deep-sleep mode interrupt enable"]
pub type WuieR = crate::BitReader;
#[doc = "Field `WUIE` writer - Wakeup from Deep-sleep mode interrupt enable"]
pub type WuieW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Error interrupt enable"]
    #[inline(always)]
    pub fn errie(&self) -> ErrieR {
        ErrieR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - IrDA mode enable"]
    #[inline(always)]
    pub fn iren(&self) -> IrenR {
        IrenR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - IrDA low-power"]
    #[inline(always)]
    pub fn irlp(&self) -> IrlpR {
        IrlpR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Half-duplex enable"]
    #[inline(always)]
    pub fn hden(&self) -> HdenR {
        HdenR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - NACK enable in Smartcard mode"]
    #[inline(always)]
    pub fn nken(&self) -> NkenR {
        NkenR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Smartcard mode enable"]
    #[inline(always)]
    pub fn scen(&self) -> ScenR {
        ScenR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - DMA enable for reception"]
    #[inline(always)]
    pub fn denr(&self) -> DenrR {
        DenrR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - DMA enable for transmission"]
    #[inline(always)]
    pub fn dent(&self) -> DentR {
        DentR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 11 - One sample bit method"]
    #[inline(always)]
    pub fn osb(&self) -> OsbR {
        OsbR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Overrun disable"]
    #[inline(always)]
    pub fn ovrd(&self) -> OvrdR {
        OvrdR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Disable DMA on reception error"]
    #[inline(always)]
    pub fn ddre(&self) -> DdreR {
        DdreR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bits 17:19 - Smartcard auto-retry number"]
    #[inline(always)]
    pub fn scrtnum(&self) -> ScrtnumR {
        ScrtnumR::new(((self.bits >> 17) & 7) as u8)
    }
    #[doc = "Bits 20:21 - Wakeup mode from Deep-sleep mode"]
    #[inline(always)]
    pub fn wum(&self) -> WumR {
        WumR::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bit 22 - Wakeup from Deep-sleep mode interrupt enable"]
    #[inline(always)]
    pub fn wuie(&self) -> WuieR {
        WuieR::new(((self.bits >> 22) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Error interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn errie(&mut self) -> ErrieW<Ctl2Spec> {
        ErrieW::new(self, 0)
    }
    #[doc = "Bit 1 - IrDA mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn iren(&mut self) -> IrenW<Ctl2Spec> {
        IrenW::new(self, 1)
    }
    #[doc = "Bit 2 - IrDA low-power"]
    #[inline(always)]
    #[must_use]
    pub fn irlp(&mut self) -> IrlpW<Ctl2Spec> {
        IrlpW::new(self, 2)
    }
    #[doc = "Bit 3 - Half-duplex enable"]
    #[inline(always)]
    #[must_use]
    pub fn hden(&mut self) -> HdenW<Ctl2Spec> {
        HdenW::new(self, 3)
    }
    #[doc = "Bit 4 - NACK enable in Smartcard mode"]
    #[inline(always)]
    #[must_use]
    pub fn nken(&mut self) -> NkenW<Ctl2Spec> {
        NkenW::new(self, 4)
    }
    #[doc = "Bit 5 - Smartcard mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn scen(&mut self) -> ScenW<Ctl2Spec> {
        ScenW::new(self, 5)
    }
    #[doc = "Bit 6 - DMA enable for reception"]
    #[inline(always)]
    #[must_use]
    pub fn denr(&mut self) -> DenrW<Ctl2Spec> {
        DenrW::new(self, 6)
    }
    #[doc = "Bit 7 - DMA enable for transmission"]
    #[inline(always)]
    #[must_use]
    pub fn dent(&mut self) -> DentW<Ctl2Spec> {
        DentW::new(self, 7)
    }
    #[doc = "Bit 11 - One sample bit method"]
    #[inline(always)]
    #[must_use]
    pub fn osb(&mut self) -> OsbW<Ctl2Spec> {
        OsbW::new(self, 11)
    }
    #[doc = "Bit 12 - Overrun disable"]
    #[inline(always)]
    #[must_use]
    pub fn ovrd(&mut self) -> OvrdW<Ctl2Spec> {
        OvrdW::new(self, 12)
    }
    #[doc = "Bit 13 - Disable DMA on reception error"]
    #[inline(always)]
    #[must_use]
    pub fn ddre(&mut self) -> DdreW<Ctl2Spec> {
        DdreW::new(self, 13)
    }
    #[doc = "Bits 17:19 - Smartcard auto-retry number"]
    #[inline(always)]
    #[must_use]
    pub fn scrtnum(&mut self) -> ScrtnumW<Ctl2Spec> {
        ScrtnumW::new(self, 17)
    }
    #[doc = "Bits 20:21 - Wakeup mode from Deep-sleep mode"]
    #[inline(always)]
    #[must_use]
    pub fn wum(&mut self) -> WumW<Ctl2Spec> {
        WumW::new(self, 20)
    }
    #[doc = "Bit 22 - Wakeup from Deep-sleep mode interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn wuie(&mut self) -> WuieW<Ctl2Spec> {
        WuieW::new(self, 22)
    }
}
#[doc = "Control register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl2::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl2::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl2Spec;
impl crate::RegisterSpec for Ctl2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl2::R`](R) reader structure"]
impl crate::Readable for Ctl2Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl2::W`](W) writer structure"]
impl crate::Writable for Ctl2Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL2 to value 0"]
impl crate::Resettable for Ctl2Spec {
    const RESET_VALUE: u32 = 0;
}
