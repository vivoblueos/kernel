#[doc = "Register `CTL1` reader"]
pub type R = crate::R<Ctl1Spec>;
#[doc = "Register `CTL1` writer"]
pub type W = crate::W<Ctl1Spec>;
#[doc = "Field `ADDR` reader - Address of the USART"]
pub type AddrR = crate::FieldReader;
#[doc = "Field `ADDR` writer - Address of the USART"]
pub type AddrW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `LBLEN` reader - LIN break frame length"]
pub type LblenR = crate::BitReader;
#[doc = "Field `LBLEN` writer - LIN break frame length"]
pub type LblenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LBDIE` reader - LIN break detection interrupt enable"]
pub type LbdieR = crate::BitReader;
#[doc = "Field `LBDIE` writer - LIN break detection interrupt enable"]
pub type LbdieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLEN` reader - CK Length"]
pub type ClenR = crate::BitReader;
#[doc = "Field `CLEN` writer - CK Length"]
pub type ClenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CPH` reader - Clock phase"]
pub type CphR = crate::BitReader;
#[doc = "Field `CPH` writer - Clock phase"]
pub type CphW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CPL` reader - Clock polarity"]
pub type CplR = crate::BitReader;
#[doc = "Field `CPL` writer - Clock polarity"]
pub type CplW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CKEN` reader - CK pin enable"]
pub type CkenR = crate::BitReader;
#[doc = "Field `CKEN` writer - CK pin enable"]
pub type CkenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STB` reader - STOP bits length"]
pub type StbR = crate::FieldReader;
#[doc = "Field `STB` writer - STOP bits length"]
pub type StbW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `LMEN` reader - LIN mode enable"]
pub type LmenR = crate::BitReader;
#[doc = "Field `LMEN` writer - LIN mode enable"]
pub type LmenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:3 - Address of the USART"]
    #[inline(always)]
    pub fn addr(&self) -> AddrR {
        AddrR::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bit 5 - LIN break frame length"]
    #[inline(always)]
    pub fn lblen(&self) -> LblenR {
        LblenR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - LIN break detection interrupt enable"]
    #[inline(always)]
    pub fn lbdie(&self) -> LbdieR {
        LbdieR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 8 - CK Length"]
    #[inline(always)]
    pub fn clen(&self) -> ClenR {
        ClenR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Clock phase"]
    #[inline(always)]
    pub fn cph(&self) -> CphR {
        CphR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Clock polarity"]
    #[inline(always)]
    pub fn cpl(&self) -> CplR {
        CplR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - CK pin enable"]
    #[inline(always)]
    pub fn cken(&self) -> CkenR {
        CkenR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bits 12:13 - STOP bits length"]
    #[inline(always)]
    pub fn stb(&self) -> StbR {
        StbR::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bit 14 - LIN mode enable"]
    #[inline(always)]
    pub fn lmen(&self) -> LmenR {
        LmenR::new(((self.bits >> 14) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:3 - Address of the USART"]
    #[inline(always)]
    #[must_use]
    pub fn addr(&mut self) -> AddrW<Ctl1Spec> {
        AddrW::new(self, 0)
    }
    #[doc = "Bit 5 - LIN break frame length"]
    #[inline(always)]
    #[must_use]
    pub fn lblen(&mut self) -> LblenW<Ctl1Spec> {
        LblenW::new(self, 5)
    }
    #[doc = "Bit 6 - LIN break detection interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn lbdie(&mut self) -> LbdieW<Ctl1Spec> {
        LbdieW::new(self, 6)
    }
    #[doc = "Bit 8 - CK Length"]
    #[inline(always)]
    #[must_use]
    pub fn clen(&mut self) -> ClenW<Ctl1Spec> {
        ClenW::new(self, 8)
    }
    #[doc = "Bit 9 - Clock phase"]
    #[inline(always)]
    #[must_use]
    pub fn cph(&mut self) -> CphW<Ctl1Spec> {
        CphW::new(self, 9)
    }
    #[doc = "Bit 10 - Clock polarity"]
    #[inline(always)]
    #[must_use]
    pub fn cpl(&mut self) -> CplW<Ctl1Spec> {
        CplW::new(self, 10)
    }
    #[doc = "Bit 11 - CK pin enable"]
    #[inline(always)]
    #[must_use]
    pub fn cken(&mut self) -> CkenW<Ctl1Spec> {
        CkenW::new(self, 11)
    }
    #[doc = "Bits 12:13 - STOP bits length"]
    #[inline(always)]
    #[must_use]
    pub fn stb(&mut self) -> StbW<Ctl1Spec> {
        StbW::new(self, 12)
    }
    #[doc = "Bit 14 - LIN mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn lmen(&mut self) -> LmenW<Ctl1Spec> {
        LmenW::new(self, 14)
    }
}
#[doc = "Control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl1Spec;
impl crate::RegisterSpec for Ctl1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl1::R`](R) reader structure"]
impl crate::Readable for Ctl1Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl1::W`](W) writer structure"]
impl crate::Writable for Ctl1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL1 to value 0"]
impl crate::Resettable for Ctl1Spec {
    const RESET_VALUE: u32 = 0;
}
