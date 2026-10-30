#[doc = "Register `STAT` reader"]
pub type R = crate::R<StatSpec>;
#[doc = "Register `STAT` writer"]
pub type W = crate::W<StatSpec>;
#[doc = "Receive Buffer Not Empty\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rbne {
    #[doc = "0: Rx buffer empty"]
    Empty = 0,
    #[doc = "1: Rx buffer not empty"]
    NotEmpty = 1,
}
impl From<Rbne> for bool {
    #[inline(always)]
    fn from(variant: Rbne) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `RBNE` reader - Receive Buffer Not Empty"]
pub type RbneR = crate::BitReader<Rbne>;
impl RbneR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Rbne {
        match self.bits {
            false => Rbne::Empty,
            true => Rbne::NotEmpty,
        }
    }
    #[doc = "Rx buffer empty"]
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        *self == Rbne::Empty
    }
    #[doc = "Rx buffer not empty"]
    #[inline(always)]
    pub fn is_not_empty(&self) -> bool {
        *self == Rbne::NotEmpty
    }
}
#[doc = "Transmit Buffer Empty\n\nValue on reset: 1"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tbe {
    #[doc = "0: Tx buffer not empty"]
    NotEmpty = 0,
    #[doc = "1: Tx buffer empty"]
    Empty = 1,
}
impl From<Tbe> for bool {
    #[inline(always)]
    fn from(variant: Tbe) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `TBE` reader - Transmit Buffer Empty"]
pub type TbeR = crate::BitReader<Tbe>;
impl TbeR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Tbe {
        match self.bits {
            false => Tbe::NotEmpty,
            true => Tbe::Empty,
        }
    }
    #[doc = "Tx buffer not empty"]
    #[inline(always)]
    pub fn is_not_empty(&self) -> bool {
        *self == Tbe::NotEmpty
    }
    #[doc = "Tx buffer empty"]
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        *self == Tbe::Empty
    }
}
#[doc = "I2S channel side\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum I2sch {
    #[doc = "0: Channel left has to be transmitted or has been received"]
    Left = 0,
    #[doc = "1: Channel right has to be transmitted or has been received"]
    Right = 1,
}
impl From<I2sch> for bool {
    #[inline(always)]
    fn from(variant: I2sch) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `I2SCH` reader - I2S channel side"]
pub type I2schR = crate::BitReader<I2sch>;
impl I2schR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> I2sch {
        match self.bits {
            false => I2sch::Left,
            true => I2sch::Right,
        }
    }
    #[doc = "Channel left has to be transmitted or has been received"]
    #[inline(always)]
    pub fn is_left(&self) -> bool {
        *self == I2sch::Left
    }
    #[doc = "Channel right has to be transmitted or has been received"]
    #[inline(always)]
    pub fn is_right(&self) -> bool {
        *self == I2sch::Right
    }
}
#[doc = "Transmission underrun error bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Txurerr {
    #[doc = "0: No underrun occurred"]
    NoUnderrun = 0,
    #[doc = "1: Underrun occurred"]
    Underrun = 1,
}
impl From<Txurerr> for bool {
    #[inline(always)]
    fn from(variant: Txurerr) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `TXURERR` reader - Transmission underrun error bit"]
pub type TxurerrR = crate::BitReader<Txurerr>;
impl TxurerrR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Txurerr {
        match self.bits {
            false => Txurerr::NoUnderrun,
            true => Txurerr::Underrun,
        }
    }
    #[doc = "No underrun occurred"]
    #[inline(always)]
    pub fn is_no_underrun(&self) -> bool {
        *self == Txurerr::NoUnderrun
    }
    #[doc = "Underrun occurred"]
    #[inline(always)]
    pub fn is_underrun(&self) -> bool {
        *self == Txurerr::Underrun
    }
}
#[doc = "SPI CRC Error Bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Crcerrr {
    #[doc = "0: CRC value received matches the SPIx_RXCRCR value"]
    Match = 0,
    #[doc = "1: CRC value received does not match the SPIx_RXCRCR value"]
    NoMatch = 1,
}
impl From<Crcerrr> for bool {
    #[inline(always)]
    fn from(variant: Crcerrr) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CRCERR` reader - SPI CRC Error Bit"]
pub type CrcerrR = crate::BitReader<Crcerrr>;
impl CrcerrR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Crcerrr {
        match self.bits {
            false => Crcerrr::Match,
            true => Crcerrr::NoMatch,
        }
    }
    #[doc = "CRC value received matches the SPIx_RXCRCR value"]
    #[inline(always)]
    pub fn is_match(&self) -> bool {
        *self == Crcerrr::Match
    }
    #[doc = "CRC value received does not match the SPIx_RXCRCR value"]
    #[inline(always)]
    pub fn is_no_match(&self) -> bool {
        *self == Crcerrr::NoMatch
    }
}
#[doc = "SPI CRC Error Bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CrcerrwWO {
    #[doc = "0: Clear CRC error"]
    Clear = 0,
}
impl From<CrcerrwWO> for bool {
    #[inline(always)]
    fn from(variant: CrcerrwWO) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CRCERR` writer - SPI CRC Error Bit"]
pub type CrcerrW<'a, REG> = crate::BitWriter<'a, REG, CrcerrwWO>;
impl<'a, REG> CrcerrW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Clear CRC error"]
    #[inline(always)]
    pub fn clear(self) -> &'a mut crate::W<REG> {
        self.variant(CrcerrwWO::Clear)
    }
}
#[doc = "SPI Configuration error\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Conferr {
    #[doc = "0: No configuration fault occurred"]
    NoFault = 0,
    #[doc = "1: Configuration fault occurred"]
    Fault = 1,
}
impl From<Conferr> for bool {
    #[inline(always)]
    fn from(variant: Conferr) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CONFERR` reader - SPI Configuration error"]
pub type ConferrR = crate::BitReader<Conferr>;
impl ConferrR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Conferr {
        match self.bits {
            false => Conferr::NoFault,
            true => Conferr::Fault,
        }
    }
    #[doc = "No configuration fault occurred"]
    #[inline(always)]
    pub fn is_no_fault(&self) -> bool {
        *self == Conferr::NoFault
    }
    #[doc = "Configuration fault occurred"]
    #[inline(always)]
    pub fn is_fault(&self) -> bool {
        *self == Conferr::Fault
    }
}
#[doc = "Reception Overrun Error Bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rxorerr {
    #[doc = "0: No overrun occurred"]
    NoOverrun = 0,
    #[doc = "1: Overrun occurred"]
    Overrun = 1,
}
impl From<Rxorerr> for bool {
    #[inline(always)]
    fn from(variant: Rxorerr) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `RXORERR` reader - Reception Overrun Error Bit"]
pub type RxorerrR = crate::BitReader<Rxorerr>;
impl RxorerrR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Rxorerr {
        match self.bits {
            false => Rxorerr::NoOverrun,
            true => Rxorerr::Overrun,
        }
    }
    #[doc = "No overrun occurred"]
    #[inline(always)]
    pub fn is_no_overrun(&self) -> bool {
        *self == Rxorerr::NoOverrun
    }
    #[doc = "Overrun occurred"]
    #[inline(always)]
    pub fn is_overrun(&self) -> bool {
        *self == Rxorerr::Overrun
    }
}
#[doc = "Transmitting On-going Bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Trans {
    #[doc = "0: SPI or I2S is idle"]
    Idle = 0,
    #[doc = "1: SPI or I2S is currently transmitting or receiving"]
    Busy = 1,
}
impl From<Trans> for bool {
    #[inline(always)]
    fn from(variant: Trans) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `TRANS` reader - Transmitting On-going Bit"]
pub type TransR = crate::BitReader<Trans>;
impl TransR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Trans {
        match self.bits {
            false => Trans::Idle,
            true => Trans::Busy,
        }
    }
    #[doc = "SPI or I2S is idle"]
    #[inline(always)]
    pub fn is_idle(&self) -> bool {
        *self == Trans::Idle
    }
    #[doc = "SPI or I2S is currently transmitting or receiving"]
    #[inline(always)]
    pub fn is_busy(&self) -> bool {
        *self == Trans::Busy
    }
}
#[doc = "Field `FERR` reader - Format Error"]
pub type FerrR = crate::BitReader;
#[doc = "Field `FERR` writer - Format Error"]
pub type FerrW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Receive Buffer Not Empty"]
    #[inline(always)]
    pub fn rbne(&self) -> RbneR {
        RbneR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Transmit Buffer Empty"]
    #[inline(always)]
    pub fn tbe(&self) -> TbeR {
        TbeR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - I2S channel side"]
    #[inline(always)]
    pub fn i2sch(&self) -> I2schR {
        I2schR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Transmission underrun error bit"]
    #[inline(always)]
    pub fn txurerr(&self) -> TxurerrR {
        TxurerrR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - SPI CRC Error Bit"]
    #[inline(always)]
    pub fn crcerr(&self) -> CrcerrR {
        CrcerrR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - SPI Configuration error"]
    #[inline(always)]
    pub fn conferr(&self) -> ConferrR {
        ConferrR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Reception Overrun Error Bit"]
    #[inline(always)]
    pub fn rxorerr(&self) -> RxorerrR {
        RxorerrR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Transmitting On-going Bit"]
    #[inline(always)]
    pub fn trans(&self) -> TransR {
        TransR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Format Error"]
    #[inline(always)]
    pub fn ferr(&self) -> FerrR {
        FerrR::new(((self.bits >> 8) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 4 - SPI CRC Error Bit"]
    #[inline(always)]
    #[must_use]
    pub fn crcerr(&mut self) -> CrcerrW<StatSpec> {
        CrcerrW::new(self, 4)
    }
    #[doc = "Bit 8 - Format Error"]
    #[inline(always)]
    #[must_use]
    pub fn ferr(&mut self) -> FerrW<StatSpec> {
        FerrW::new(self, 8)
    }
}
#[doc = "status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`stat::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
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
#[doc = "`reset()` method sets STAT to value 0x02"]
impl crate::Resettable for StatSpec {
    const RESET_VALUE: u32 = 0x02;
}
