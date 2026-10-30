#[doc = "Register `CH1CTL` reader"]
pub type R = crate::R<Ch1ctlSpec>;
#[doc = "Register `CH1CTL` writer"]
pub type W = crate::W<Ch1ctlSpec>;
#[doc = "Channel enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Chen {
    #[doc = "0: Channel disabled"]
    Disabled = 0,
    #[doc = "1: Channel enabled"]
    Enabled = 1,
}
impl From<Chen> for bool {
    #[inline(always)]
    fn from(variant: Chen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CHEN` reader - Channel enable"]
pub type ChenR = crate::BitReader<Chen>;
impl ChenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Chen {
        match self.bits {
            false => Chen::Disabled,
            true => Chen::Enabled,
        }
    }
    #[doc = "Channel disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Chen::Disabled
    }
    #[doc = "Channel enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Chen::Enabled
    }
}
#[doc = "Field `CHEN` writer - Channel enable"]
pub type ChenW<'a, REG> = crate::BitWriter<'a, REG, Chen>;
impl<'a, REG> ChenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Channel disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Chen::Disabled)
    }
    #[doc = "Channel enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Chen::Enabled)
    }
}
#[doc = "Enable bit for channel full transfer finish interrupt\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ftfie {
    #[doc = "0: Full transfer interrupt disabled"]
    Disabled = 0,
    #[doc = "1: Full transfer interrupt enabled"]
    Enabled = 1,
}
impl From<Ftfie> for bool {
    #[inline(always)]
    fn from(variant: Ftfie) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `FTFIE` reader - Enable bit for channel full transfer finish interrupt"]
pub type FtfieR = crate::BitReader<Ftfie>;
impl FtfieR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ftfie {
        match self.bits {
            false => Ftfie::Disabled,
            true => Ftfie::Enabled,
        }
    }
    #[doc = "Full transfer interrupt disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Ftfie::Disabled
    }
    #[doc = "Full transfer interrupt enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Ftfie::Enabled
    }
}
#[doc = "Field `FTFIE` writer - Enable bit for channel full transfer finish interrupt"]
pub type FtfieW<'a, REG> = crate::BitWriter<'a, REG, Ftfie>;
impl<'a, REG> FtfieW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Full transfer interrupt disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ftfie::Disabled)
    }
    #[doc = "Full transfer interrupt enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ftfie::Enabled)
    }
}
#[doc = "Enable bit for channel half transfer finish interrupt\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Htfie {
    #[doc = "0: Half transfer interrupt disabled"]
    Disabled = 0,
    #[doc = "1: Half transfer interrupt enabled"]
    Enabled = 1,
}
impl From<Htfie> for bool {
    #[inline(always)]
    fn from(variant: Htfie) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `HTFIE` reader - Enable bit for channel half transfer finish interrupt"]
pub type HtfieR = crate::BitReader<Htfie>;
impl HtfieR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Htfie {
        match self.bits {
            false => Htfie::Disabled,
            true => Htfie::Enabled,
        }
    }
    #[doc = "Half transfer interrupt disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Htfie::Disabled
    }
    #[doc = "Half transfer interrupt enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Htfie::Enabled
    }
}
#[doc = "Field `HTFIE` writer - Enable bit for channel half transfer finish interrupt"]
pub type HtfieW<'a, REG> = crate::BitWriter<'a, REG, Htfie>;
impl<'a, REG> HtfieW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Half transfer interrupt disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Htfie::Disabled)
    }
    #[doc = "Half transfer interrupt enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Htfie::Enabled)
    }
}
#[doc = "Enable bit for channel error interrupt\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Errie {
    #[doc = "0: Transfer error interrupt disabled"]
    Disabled = 0,
    #[doc = "1: Transfer error interrupt enabled"]
    Enabled = 1,
}
impl From<Errie> for bool {
    #[inline(always)]
    fn from(variant: Errie) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `ERRIE` reader - Enable bit for channel error interrupt"]
pub type ErrieR = crate::BitReader<Errie>;
impl ErrieR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Errie {
        match self.bits {
            false => Errie::Disabled,
            true => Errie::Enabled,
        }
    }
    #[doc = "Transfer error interrupt disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Errie::Disabled
    }
    #[doc = "Transfer error interrupt enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Errie::Enabled
    }
}
#[doc = "Field `ERRIE` writer - Enable bit for channel error interrupt"]
pub type ErrieW<'a, REG> = crate::BitWriter<'a, REG, Errie>;
impl<'a, REG> ErrieW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Transfer error interrupt disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Errie::Disabled)
    }
    #[doc = "Transfer error interrupt enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Errie::Enabled)
    }
}
#[doc = "Transfer direction\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    #[doc = "0: Read from peripheral"]
    FromPeripheral = 0,
    #[doc = "1: Read from memory"]
    FromMemory = 1,
}
impl From<Dir> for bool {
    #[inline(always)]
    fn from(variant: Dir) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `DIR` reader - Transfer direction"]
pub type DirR = crate::BitReader<Dir>;
impl DirR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Dir {
        match self.bits {
            false => Dir::FromPeripheral,
            true => Dir::FromMemory,
        }
    }
    #[doc = "Read from peripheral"]
    #[inline(always)]
    pub fn is_from_peripheral(&self) -> bool {
        *self == Dir::FromPeripheral
    }
    #[doc = "Read from memory"]
    #[inline(always)]
    pub fn is_from_memory(&self) -> bool {
        *self == Dir::FromMemory
    }
}
#[doc = "Field `DIR` writer - Transfer direction"]
pub type DirW<'a, REG> = crate::BitWriter<'a, REG, Dir>;
impl<'a, REG> DirW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Read from peripheral"]
    #[inline(always)]
    pub fn from_peripheral(self) -> &'a mut crate::W<REG> {
        self.variant(Dir::FromPeripheral)
    }
    #[doc = "Read from memory"]
    #[inline(always)]
    pub fn from_memory(self) -> &'a mut crate::W<REG> {
        self.variant(Dir::FromMemory)
    }
}
#[doc = "Circular mode enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cmen {
    #[doc = "0: Circular buffer disabled"]
    Disabled = 0,
    #[doc = "1: Circular buffer enabled"]
    Enabled = 1,
}
impl From<Cmen> for bool {
    #[inline(always)]
    fn from(variant: Cmen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CMEN` reader - Circular mode enable"]
pub type CmenR = crate::BitReader<Cmen>;
impl CmenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Cmen {
        match self.bits {
            false => Cmen::Disabled,
            true => Cmen::Enabled,
        }
    }
    #[doc = "Circular buffer disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Cmen::Disabled
    }
    #[doc = "Circular buffer enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Cmen::Enabled
    }
}
#[doc = "Field `CMEN` writer - Circular mode enable"]
pub type CmenW<'a, REG> = crate::BitWriter<'a, REG, Cmen>;
impl<'a, REG> CmenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Circular buffer disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Cmen::Disabled)
    }
    #[doc = "Circular buffer enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Cmen::Enabled)
    }
}
#[doc = "Next address generation algorithm of peripheral\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pnaga {
    #[doc = "0: Fixed address mode"]
    Fixed = 0,
    #[doc = "1: Increment address mode"]
    Increment = 1,
}
impl From<Pnaga> for bool {
    #[inline(always)]
    fn from(variant: Pnaga) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `PNAGA` reader - Next address generation algorithm of peripheral"]
pub type PnagaR = crate::BitReader<Pnaga>;
impl PnagaR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Pnaga {
        match self.bits {
            false => Pnaga::Fixed,
            true => Pnaga::Increment,
        }
    }
    #[doc = "Fixed address mode"]
    #[inline(always)]
    pub fn is_fixed(&self) -> bool {
        *self == Pnaga::Fixed
    }
    #[doc = "Increment address mode"]
    #[inline(always)]
    pub fn is_increment(&self) -> bool {
        *self == Pnaga::Increment
    }
}
#[doc = "Field `PNAGA` writer - Next address generation algorithm of peripheral"]
pub type PnagaW<'a, REG> = crate::BitWriter<'a, REG, Pnaga>;
impl<'a, REG> PnagaW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Fixed address mode"]
    #[inline(always)]
    pub fn fixed(self) -> &'a mut crate::W<REG> {
        self.variant(Pnaga::Fixed)
    }
    #[doc = "Increment address mode"]
    #[inline(always)]
    pub fn increment(self) -> &'a mut crate::W<REG> {
        self.variant(Pnaga::Increment)
    }
}
#[doc = "Field `MNAGA` reader - Next address generation algorithm of memory"]
pub use PnagaR as MnagaR;
#[doc = "Field `MNAGA` writer - Next address generation algorithm of memory"]
pub use PnagaW as MnagaW;
#[doc = "Transfer data size of peripheral\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Pwidth {
    #[doc = "0: 8-bit size"]
    Bits8 = 0,
    #[doc = "1: 16-bit size"]
    Bits16 = 1,
    #[doc = "2: 32-bit size"]
    Bits32 = 2,
}
impl From<Pwidth> for u8 {
    #[inline(always)]
    fn from(variant: Pwidth) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Pwidth {
    type Ux = u8;
}
#[doc = "Field `PWIDTH` reader - Transfer data size of peripheral"]
pub type PwidthR = crate::FieldReader<Pwidth>;
impl PwidthR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Option<Pwidth> {
        match self.bits {
            0 => Some(Pwidth::Bits8),
            1 => Some(Pwidth::Bits16),
            2 => Some(Pwidth::Bits32),
            _ => None,
        }
    }
    #[doc = "8-bit size"]
    #[inline(always)]
    pub fn is_bits8(&self) -> bool {
        *self == Pwidth::Bits8
    }
    #[doc = "16-bit size"]
    #[inline(always)]
    pub fn is_bits16(&self) -> bool {
        *self == Pwidth::Bits16
    }
    #[doc = "32-bit size"]
    #[inline(always)]
    pub fn is_bits32(&self) -> bool {
        *self == Pwidth::Bits32
    }
}
#[doc = "Field `PWIDTH` writer - Transfer data size of peripheral"]
pub type PwidthW<'a, REG> = crate::FieldWriter<'a, REG, 2, Pwidth>;
impl<'a, REG> PwidthW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "8-bit size"]
    #[inline(always)]
    pub fn bits8(self) -> &'a mut crate::W<REG> {
        self.variant(Pwidth::Bits8)
    }
    #[doc = "16-bit size"]
    #[inline(always)]
    pub fn bits16(self) -> &'a mut crate::W<REG> {
        self.variant(Pwidth::Bits16)
    }
    #[doc = "32-bit size"]
    #[inline(always)]
    pub fn bits32(self) -> &'a mut crate::W<REG> {
        self.variant(Pwidth::Bits32)
    }
}
#[doc = "Field `MWIDTH` reader - Transfer data size of memory"]
pub use PwidthR as MwidthR;
#[doc = "Field `MWIDTH` writer - Transfer data size of memory"]
pub use PwidthW as MwidthW;
#[doc = "Priority level\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Prio {
    #[doc = "0: Low priority"]
    Low = 0,
    #[doc = "1: Medium priority"]
    Medium = 1,
    #[doc = "2: High priority"]
    High = 2,
    #[doc = "3: Very high priority"]
    VeryHigh = 3,
}
impl From<Prio> for u8 {
    #[inline(always)]
    fn from(variant: Prio) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Prio {
    type Ux = u8;
}
#[doc = "Field `PRIO` reader - Priority level"]
pub type PrioR = crate::FieldReader<Prio>;
impl PrioR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Prio {
        match self.bits {
            0 => Prio::Low,
            1 => Prio::Medium,
            2 => Prio::High,
            3 => Prio::VeryHigh,
            _ => unreachable!(),
        }
    }
    #[doc = "Low priority"]
    #[inline(always)]
    pub fn is_low(&self) -> bool {
        *self == Prio::Low
    }
    #[doc = "Medium priority"]
    #[inline(always)]
    pub fn is_medium(&self) -> bool {
        *self == Prio::Medium
    }
    #[doc = "High priority"]
    #[inline(always)]
    pub fn is_high(&self) -> bool {
        *self == Prio::High
    }
    #[doc = "Very high priority"]
    #[inline(always)]
    pub fn is_very_high(&self) -> bool {
        *self == Prio::VeryHigh
    }
}
#[doc = "Field `PRIO` writer - Priority level"]
pub type PrioW<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, Prio>;
impl<'a, REG> PrioW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Low priority"]
    #[inline(always)]
    pub fn low(self) -> &'a mut crate::W<REG> {
        self.variant(Prio::Low)
    }
    #[doc = "Medium priority"]
    #[inline(always)]
    pub fn medium(self) -> &'a mut crate::W<REG> {
        self.variant(Prio::Medium)
    }
    #[doc = "High priority"]
    #[inline(always)]
    pub fn high(self) -> &'a mut crate::W<REG> {
        self.variant(Prio::High)
    }
    #[doc = "Very high priority"]
    #[inline(always)]
    pub fn very_high(self) -> &'a mut crate::W<REG> {
        self.variant(Prio::VeryHigh)
    }
}
#[doc = "Memory to Memory Mode\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum M2m {
    #[doc = "0: Memory to memory mode disabled"]
    Disabled = 0,
    #[doc = "1: Memory to memory mode enabled"]
    Enabled = 1,
}
impl From<M2m> for bool {
    #[inline(always)]
    fn from(variant: M2m) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `M2M` reader - Memory to Memory Mode"]
pub type M2mR = crate::BitReader<M2m>;
impl M2mR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> M2m {
        match self.bits {
            false => M2m::Disabled,
            true => M2m::Enabled,
        }
    }
    #[doc = "Memory to memory mode disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == M2m::Disabled
    }
    #[doc = "Memory to memory mode enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == M2m::Enabled
    }
}
#[doc = "Field `M2M` writer - Memory to Memory Mode"]
pub type M2mW<'a, REG> = crate::BitWriter<'a, REG, M2m>;
impl<'a, REG> M2mW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Memory to memory mode disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(M2m::Disabled)
    }
    #[doc = "Memory to memory mode enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(M2m::Enabled)
    }
}
impl R {
    #[doc = "Bit 0 - Channel enable"]
    #[inline(always)]
    pub fn chen(&self) -> ChenR {
        ChenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Enable bit for channel full transfer finish interrupt"]
    #[inline(always)]
    pub fn ftfie(&self) -> FtfieR {
        FtfieR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Enable bit for channel half transfer finish interrupt"]
    #[inline(always)]
    pub fn htfie(&self) -> HtfieR {
        HtfieR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Enable bit for channel error interrupt"]
    #[inline(always)]
    pub fn errie(&self) -> ErrieR {
        ErrieR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Transfer direction"]
    #[inline(always)]
    pub fn dir(&self) -> DirR {
        DirR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Circular mode enable"]
    #[inline(always)]
    pub fn cmen(&self) -> CmenR {
        CmenR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Next address generation algorithm of peripheral"]
    #[inline(always)]
    pub fn pnaga(&self) -> PnagaR {
        PnagaR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Next address generation algorithm of memory"]
    #[inline(always)]
    pub fn mnaga(&self) -> MnagaR {
        MnagaR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:9 - Transfer data size of peripheral"]
    #[inline(always)]
    pub fn pwidth(&self) -> PwidthR {
        PwidthR::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bits 10:11 - Transfer data size of memory"]
    #[inline(always)]
    pub fn mwidth(&self) -> MwidthR {
        MwidthR::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bits 12:13 - Priority level"]
    #[inline(always)]
    pub fn prio(&self) -> PrioR {
        PrioR::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bit 14 - Memory to Memory Mode"]
    #[inline(always)]
    pub fn m2m(&self) -> M2mR {
        M2mR::new(((self.bits >> 14) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Channel enable"]
    #[inline(always)]
    #[must_use]
    pub fn chen(&mut self) -> ChenW<Ch1ctlSpec> {
        ChenW::new(self, 0)
    }
    #[doc = "Bit 1 - Enable bit for channel full transfer finish interrupt"]
    #[inline(always)]
    #[must_use]
    pub fn ftfie(&mut self) -> FtfieW<Ch1ctlSpec> {
        FtfieW::new(self, 1)
    }
    #[doc = "Bit 2 - Enable bit for channel half transfer finish interrupt"]
    #[inline(always)]
    #[must_use]
    pub fn htfie(&mut self) -> HtfieW<Ch1ctlSpec> {
        HtfieW::new(self, 2)
    }
    #[doc = "Bit 3 - Enable bit for channel error interrupt"]
    #[inline(always)]
    #[must_use]
    pub fn errie(&mut self) -> ErrieW<Ch1ctlSpec> {
        ErrieW::new(self, 3)
    }
    #[doc = "Bit 4 - Transfer direction"]
    #[inline(always)]
    #[must_use]
    pub fn dir(&mut self) -> DirW<Ch1ctlSpec> {
        DirW::new(self, 4)
    }
    #[doc = "Bit 5 - Circular mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmen(&mut self) -> CmenW<Ch1ctlSpec> {
        CmenW::new(self, 5)
    }
    #[doc = "Bit 6 - Next address generation algorithm of peripheral"]
    #[inline(always)]
    #[must_use]
    pub fn pnaga(&mut self) -> PnagaW<Ch1ctlSpec> {
        PnagaW::new(self, 6)
    }
    #[doc = "Bit 7 - Next address generation algorithm of memory"]
    #[inline(always)]
    #[must_use]
    pub fn mnaga(&mut self) -> MnagaW<Ch1ctlSpec> {
        MnagaW::new(self, 7)
    }
    #[doc = "Bits 8:9 - Transfer data size of peripheral"]
    #[inline(always)]
    #[must_use]
    pub fn pwidth(&mut self) -> PwidthW<Ch1ctlSpec> {
        PwidthW::new(self, 8)
    }
    #[doc = "Bits 10:11 - Transfer data size of memory"]
    #[inline(always)]
    #[must_use]
    pub fn mwidth(&mut self) -> MwidthW<Ch1ctlSpec> {
        MwidthW::new(self, 10)
    }
    #[doc = "Bits 12:13 - Priority level"]
    #[inline(always)]
    #[must_use]
    pub fn prio(&mut self) -> PrioW<Ch1ctlSpec> {
        PrioW::new(self, 12)
    }
    #[doc = "Bit 14 - Memory to Memory Mode"]
    #[inline(always)]
    #[must_use]
    pub fn m2m(&mut self) -> M2mW<Ch1ctlSpec> {
        M2mW::new(self, 14)
    }
}
#[doc = "Channel 1 control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch1ctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch1ctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ch1ctlSpec;
impl crate::RegisterSpec for Ch1ctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch1ctl::R`](R) reader structure"]
impl crate::Readable for Ch1ctlSpec {}
#[doc = "`write(|w| ..)` method takes [`ch1ctl::W`](W) writer structure"]
impl crate::Writable for Ch1ctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CH1CTL to value 0"]
impl crate::Resettable for Ch1ctlSpec {
    const RESET_VALUE: u32 = 0;
}
