#[doc = "Register `RFCS` reader"]
pub type R = crate::R<RfcsSpec>;
#[doc = "Register `RFCS` writer"]
pub type W = crate::W<RfcsSpec>;
#[doc = "Field `ELNACK` reader - Early NACK when smartcard mode is selected"]
pub type ElnackR = crate::BitReader;
#[doc = "Field `ELNACK` writer - Early NACK when smartcard mode is selected"]
pub type ElnackW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFEN` reader - Receive FIFO enable"]
pub type RfenR = crate::BitReader;
#[doc = "Field `RFEN` writer - Receive FIFO enable"]
pub type RfenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFFIE` reader - Receive FIFO full interrupt enable"]
pub type RffieR = crate::BitReader;
#[doc = "Field `RFFIE` writer - Receive FIFO full interrupt enable"]
pub type RffieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFE` reader - Receive FIFO empty flag"]
pub type RfeR = crate::BitReader;
#[doc = "Field `RFF` reader - Receive FIFO full flag"]
pub type RffR = crate::BitReader;
#[doc = "Field `RFCNT` reader - Receive FIFO counter number"]
pub type RfcntR = crate::FieldReader;
#[doc = "Field `RFFINT` reader - Receive FIFO full interrupt flag"]
pub type RffintR = crate::BitReader;
#[doc = "Field `RFFINT` writer - Receive FIFO full interrupt flag"]
pub type RffintW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Early NACK when smartcard mode is selected"]
    #[inline(always)]
    pub fn elnack(&self) -> ElnackR {
        ElnackR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 8 - Receive FIFO enable"]
    #[inline(always)]
    pub fn rfen(&self) -> RfenR {
        RfenR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Receive FIFO full interrupt enable"]
    #[inline(always)]
    pub fn rffie(&self) -> RffieR {
        RffieR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Receive FIFO empty flag"]
    #[inline(always)]
    pub fn rfe(&self) -> RfeR {
        RfeR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Receive FIFO full flag"]
    #[inline(always)]
    pub fn rff(&self) -> RffR {
        RffR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bits 12:14 - Receive FIFO counter number"]
    #[inline(always)]
    pub fn rfcnt(&self) -> RfcntR {
        RfcntR::new(((self.bits >> 12) & 7) as u8)
    }
    #[doc = "Bit 15 - Receive FIFO full interrupt flag"]
    #[inline(always)]
    pub fn rffint(&self) -> RffintR {
        RffintR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Early NACK when smartcard mode is selected"]
    #[inline(always)]
    #[must_use]
    pub fn elnack(&mut self) -> ElnackW<RfcsSpec> {
        ElnackW::new(self, 0)
    }
    #[doc = "Bit 8 - Receive FIFO enable"]
    #[inline(always)]
    #[must_use]
    pub fn rfen(&mut self) -> RfenW<RfcsSpec> {
        RfenW::new(self, 8)
    }
    #[doc = "Bit 9 - Receive FIFO full interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rffie(&mut self) -> RffieW<RfcsSpec> {
        RffieW::new(self, 9)
    }
    #[doc = "Bit 15 - Receive FIFO full interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn rffint(&mut self) -> RffintW<RfcsSpec> {
        RffintW::new(self, 15)
    }
}
#[doc = "receive FIFO control and status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfcs::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rfcs::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RfcsSpec;
impl crate::RegisterSpec for RfcsSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rfcs::R`](R) reader structure"]
impl crate::Readable for RfcsSpec {}
#[doc = "`write(|w| ..)` method takes [`rfcs::W`](W) writer structure"]
impl crate::Writable for RfcsSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets RFCS to value 0x0400"]
impl crate::Resettable for RfcsSpec {
    const RESET_VALUE: u32 = 0x0400;
}
