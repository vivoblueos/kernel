#[doc = "Register `STAT` reader"]
pub type R = crate::R<StatSpec>;
#[doc = "Register `STAT` writer"]
pub type W = crate::W<StatSpec>;
#[doc = "Field `IWS` reader - Initial working state"]
pub type IwsR = crate::BitReader;
#[doc = "Field `SLPWS` reader - Sleep working state"]
pub type SlpwsR = crate::BitReader;
#[doc = "Field `ERRIF` reader - Error interrupt flag"]
pub type ErrifR = crate::BitReader;
#[doc = "Field `ERRIF` writer - Error interrupt flag"]
pub type ErrifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WUIF` reader - Status change interrupt flag of wakeup from sleep working mode"]
pub type WuifR = crate::BitReader;
#[doc = "Field `WUIF` writer - Status change interrupt flag of wakeup from sleep working mode"]
pub type WuifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLPIF` reader - Status change interrupt flag of sleep working mode entering"]
pub type SlpifR = crate::BitReader;
#[doc = "Field `SLPIF` writer - Status change interrupt flag of sleep working mode entering"]
pub type SlpifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TS` reader - Transmitting state"]
pub type TsR = crate::BitReader;
#[doc = "Field `RS` reader - Receiving state"]
pub type RsR = crate::BitReader;
#[doc = "Field `LASTRX` reader - Last sample value of RX pin"]
pub type LastrxR = crate::BitReader;
#[doc = "Field `RXL` reader - RX level"]
pub type RxlR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Initial working state"]
    #[inline(always)]
    pub fn iws(&self) -> IwsR {
        IwsR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Sleep working state"]
    #[inline(always)]
    pub fn slpws(&self) -> SlpwsR {
        SlpwsR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Error interrupt flag"]
    #[inline(always)]
    pub fn errif(&self) -> ErrifR {
        ErrifR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Status change interrupt flag of wakeup from sleep working mode"]
    #[inline(always)]
    pub fn wuif(&self) -> WuifR {
        WuifR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Status change interrupt flag of sleep working mode entering"]
    #[inline(always)]
    pub fn slpif(&self) -> SlpifR {
        SlpifR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 8 - Transmitting state"]
    #[inline(always)]
    pub fn ts(&self) -> TsR {
        TsR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Receiving state"]
    #[inline(always)]
    pub fn rs(&self) -> RsR {
        RsR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Last sample value of RX pin"]
    #[inline(always)]
    pub fn lastrx(&self) -> LastrxR {
        LastrxR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - RX level"]
    #[inline(always)]
    pub fn rxl(&self) -> RxlR {
        RxlR::new(((self.bits >> 11) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 2 - Error interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn errif(&mut self) -> ErrifW<StatSpec> {
        ErrifW::new(self, 2)
    }
    #[doc = "Bit 3 - Status change interrupt flag of wakeup from sleep working mode"]
    #[inline(always)]
    #[must_use]
    pub fn wuif(&mut self) -> WuifW<StatSpec> {
        WuifW::new(self, 3)
    }
    #[doc = "Bit 4 - Status change interrupt flag of sleep working mode entering"]
    #[inline(always)]
    #[must_use]
    pub fn slpif(&mut self) -> SlpifW<StatSpec> {
        SlpifW::new(self, 4)
    }
}
#[doc = "Status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`stat::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct StatSpec;
impl crate::RegisterSpec for StatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`stat::R`](R) reader structure"]
impl crate::Readable for StatSpec {}
#[doc = "`write(|w| ..)` method takes [`stat::W`](W) writer structure"]
impl crate::Writable for StatSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets STAT to value 0x0c02"]
impl crate::Resettable for StatSpec {
    const RESET_VALUE: u32 = 0x0c02;
}
