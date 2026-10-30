#[doc = "Register `CTL` reader"]
pub type R = crate::R<CtlSpec>;
#[doc = "Register `CTL` writer"]
pub type W = crate::W<CtlSpec>;
#[doc = "Field `IWMOD` reader - Initial working mode"]
pub type IwmodR = crate::BitReader;
#[doc = "Field `IWMOD` writer - Initial working mode"]
pub type IwmodW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLPWMOD` reader - Sleep working mode"]
pub type SlpwmodR = crate::BitReader;
#[doc = "Field `SLPWMOD` writer - Sleep working mode"]
pub type SlpwmodW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TFO` reader - Transmit FIFO order"]
pub type TfoR = crate::BitReader;
#[doc = "Field `TFO` writer - Transmit FIFO order"]
pub type TfoW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFOD` reader - Receive FIFO overwrite disable"]
pub type RfodR = crate::BitReader;
#[doc = "Field `RFOD` writer - Receive FIFO overwrite disable"]
pub type RfodW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ARD` reader - Automatic retransmission disable"]
pub type ArdR = crate::BitReader;
#[doc = "Field `ARD` writer - Automatic retransmission disable"]
pub type ArdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AWU` reader - Automatic wakeup"]
pub type AwuR = crate::BitReader;
#[doc = "Field `AWU` writer - Automatic wakeup"]
pub type AwuW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ABOR` reader - Automatic bus-off recovery"]
pub type AborR = crate::BitReader;
#[doc = "Field `ABOR` writer - Automatic bus-off recovery"]
pub type AborW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TTC` reader - Time-triggered communication"]
pub type TtcR = crate::BitReader;
#[doc = "Field `TTC` writer - Time-triggered communication"]
pub type TtcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SWRST` reader - Software reset"]
pub type SwrstR = crate::BitReader;
#[doc = "Field `SWRST` writer - Software reset"]
pub type SwrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DFZ` reader - Debug freeze"]
pub type DfzR = crate::BitReader;
#[doc = "Field `DFZ` writer - Debug freeze"]
pub type DfzW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Initial working mode"]
    #[inline(always)]
    pub fn iwmod(&self) -> IwmodR {
        IwmodR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Sleep working mode"]
    #[inline(always)]
    pub fn slpwmod(&self) -> SlpwmodR {
        SlpwmodR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Transmit FIFO order"]
    #[inline(always)]
    pub fn tfo(&self) -> TfoR {
        TfoR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Receive FIFO overwrite disable"]
    #[inline(always)]
    pub fn rfod(&self) -> RfodR {
        RfodR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Automatic retransmission disable"]
    #[inline(always)]
    pub fn ard(&self) -> ArdR {
        ArdR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Automatic wakeup"]
    #[inline(always)]
    pub fn awu(&self) -> AwuR {
        AwuR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Automatic bus-off recovery"]
    #[inline(always)]
    pub fn abor(&self) -> AborR {
        AborR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Time-triggered communication"]
    #[inline(always)]
    pub fn ttc(&self) -> TtcR {
        TtcR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 15 - Software reset"]
    #[inline(always)]
    pub fn swrst(&self) -> SwrstR {
        SwrstR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Debug freeze"]
    #[inline(always)]
    pub fn dfz(&self) -> DfzR {
        DfzR::new(((self.bits >> 16) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Initial working mode"]
    #[inline(always)]
    #[must_use]
    pub fn iwmod(&mut self) -> IwmodW<CtlSpec> {
        IwmodW::new(self, 0)
    }
    #[doc = "Bit 1 - Sleep working mode"]
    #[inline(always)]
    #[must_use]
    pub fn slpwmod(&mut self) -> SlpwmodW<CtlSpec> {
        SlpwmodW::new(self, 1)
    }
    #[doc = "Bit 2 - Transmit FIFO order"]
    #[inline(always)]
    #[must_use]
    pub fn tfo(&mut self) -> TfoW<CtlSpec> {
        TfoW::new(self, 2)
    }
    #[doc = "Bit 3 - Receive FIFO overwrite disable"]
    #[inline(always)]
    #[must_use]
    pub fn rfod(&mut self) -> RfodW<CtlSpec> {
        RfodW::new(self, 3)
    }
    #[doc = "Bit 4 - Automatic retransmission disable"]
    #[inline(always)]
    #[must_use]
    pub fn ard(&mut self) -> ArdW<CtlSpec> {
        ArdW::new(self, 4)
    }
    #[doc = "Bit 5 - Automatic wakeup"]
    #[inline(always)]
    #[must_use]
    pub fn awu(&mut self) -> AwuW<CtlSpec> {
        AwuW::new(self, 5)
    }
    #[doc = "Bit 6 - Automatic bus-off recovery"]
    #[inline(always)]
    #[must_use]
    pub fn abor(&mut self) -> AborW<CtlSpec> {
        AborW::new(self, 6)
    }
    #[doc = "Bit 7 - Time-triggered communication"]
    #[inline(always)]
    #[must_use]
    pub fn ttc(&mut self) -> TtcW<CtlSpec> {
        TtcW::new(self, 7)
    }
    #[doc = "Bit 15 - Software reset"]
    #[inline(always)]
    #[must_use]
    pub fn swrst(&mut self) -> SwrstW<CtlSpec> {
        SwrstW::new(self, 15)
    }
    #[doc = "Bit 16 - Debug freeze"]
    #[inline(always)]
    #[must_use]
    pub fn dfz(&mut self) -> DfzW<CtlSpec> {
        DfzW::new(self, 16)
    }
}
#[doc = "Control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CtlSpec;
impl crate::RegisterSpec for CtlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl::R`](R) reader structure"]
impl crate::Readable for CtlSpec {}
#[doc = "`write(|w| ..)` method takes [`ctl::W`](W) writer structure"]
impl crate::Writable for CtlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL to value 0x0001_0002"]
impl crate::Resettable for CtlSpec {
    const RESET_VALUE: u32 = 0x0001_0002;
}
