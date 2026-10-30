#[doc = "Register `CTL1` reader"]
pub type R = crate::R<Ctl1Spec>;
#[doc = "Register `CTL1` writer"]
pub type W = crate::W<Ctl1Spec>;
#[doc = "Commutation control shadow enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ccse {
    #[doc = "0: The shadow registers for CHxEN, CHxNEN and CHxCOMCTL bits are disabled"]
    NotPreloaded = 0,
    #[doc = "1: The shadow registers for CHxEN, CHxNEN and CHxCOMCTL bits are enabled"]
    Preloaded = 1,
}
impl From<Ccse> for bool {
    #[inline(always)]
    fn from(variant: Ccse) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CCSE` reader - Commutation control shadow enable"]
pub type CcseR = crate::BitReader<Ccse>;
impl CcseR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ccse {
        match self.bits {
            false => Ccse::NotPreloaded,
            true => Ccse::Preloaded,
        }
    }
    #[doc = "The shadow registers for CHxEN, CHxNEN and CHxCOMCTL bits are disabled"]
    #[inline(always)]
    pub fn is_not_preloaded(&self) -> bool {
        *self == Ccse::NotPreloaded
    }
    #[doc = "The shadow registers for CHxEN, CHxNEN and CHxCOMCTL bits are enabled"]
    #[inline(always)]
    pub fn is_preloaded(&self) -> bool {
        *self == Ccse::Preloaded
    }
}
#[doc = "Field `CCSE` writer - Commutation control shadow enable"]
pub type CcseW<'a, REG> = crate::BitWriter<'a, REG, Ccse>;
impl<'a, REG> CcseW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "The shadow registers for CHxEN, CHxNEN and CHxCOMCTL bits are disabled"]
    #[inline(always)]
    pub fn not_preloaded(self) -> &'a mut crate::W<REG> {
        self.variant(Ccse::NotPreloaded)
    }
    #[doc = "The shadow registers for CHxEN, CHxNEN and CHxCOMCTL bits are enabled"]
    #[inline(always)]
    pub fn preloaded(self) -> &'a mut crate::W<REG> {
        self.variant(Ccse::Preloaded)
    }
}
#[doc = "Commutation control shadow register update control\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ccuc {
    #[doc = "0: Capture/compare are updated only by setting the CMTG bit"]
    Default = 0,
    #[doc = "1: Capture/compare are updated by setting the CMTG bit or when an rising edge occurs on TRGI"]
    WithRisingEdge = 1,
}
impl From<Ccuc> for bool {
    #[inline(always)]
    fn from(variant: Ccuc) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CCUC` reader - Commutation control shadow register update control"]
pub type CcucR = crate::BitReader<Ccuc>;
impl CcucR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ccuc {
        match self.bits {
            false => Ccuc::Default,
            true => Ccuc::WithRisingEdge,
        }
    }
    #[doc = "Capture/compare are updated only by setting the CMTG bit"]
    #[inline(always)]
    pub fn is_default(&self) -> bool {
        *self == Ccuc::Default
    }
    #[doc = "Capture/compare are updated by setting the CMTG bit or when an rising edge occurs on TRGI"]
    #[inline(always)]
    pub fn is_with_rising_edge(&self) -> bool {
        *self == Ccuc::WithRisingEdge
    }
}
#[doc = "Field `CCUC` writer - Commutation control shadow register update control"]
pub type CcucW<'a, REG> = crate::BitWriter<'a, REG, Ccuc>;
impl<'a, REG> CcucW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Capture/compare are updated only by setting the CMTG bit"]
    #[inline(always)]
    pub fn default(self) -> &'a mut crate::W<REG> {
        self.variant(Ccuc::Default)
    }
    #[doc = "Capture/compare are updated by setting the CMTG bit or when an rising edge occurs on TRGI"]
    #[inline(always)]
    pub fn with_rising_edge(self) -> &'a mut crate::W<REG> {
        self.variant(Ccuc::WithRisingEdge)
    }
}
#[doc = "DMA request source selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dmas {
    #[doc = "0: CCx DMA request sent when CCx event occurs"]
    OnCompare = 0,
    #[doc = "1: CCx DMA request sent when update event occurs"]
    OnUpdate = 1,
}
impl From<Dmas> for bool {
    #[inline(always)]
    fn from(variant: Dmas) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `DMAS` reader - DMA request source selection"]
pub type DmasR = crate::BitReader<Dmas>;
impl DmasR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Dmas {
        match self.bits {
            false => Dmas::OnCompare,
            true => Dmas::OnUpdate,
        }
    }
    #[doc = "CCx DMA request sent when CCx event occurs"]
    #[inline(always)]
    pub fn is_on_compare(&self) -> bool {
        *self == Dmas::OnCompare
    }
    #[doc = "CCx DMA request sent when update event occurs"]
    #[inline(always)]
    pub fn is_on_update(&self) -> bool {
        *self == Dmas::OnUpdate
    }
}
#[doc = "Field `DMAS` writer - DMA request source selection"]
pub type DmasW<'a, REG> = crate::BitWriter<'a, REG, Dmas>;
impl<'a, REG> DmasW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "CCx DMA request sent when CCx event occurs"]
    #[inline(always)]
    pub fn on_compare(self) -> &'a mut crate::W<REG> {
        self.variant(Dmas::OnCompare)
    }
    #[doc = "CCx DMA request sent when update event occurs"]
    #[inline(always)]
    pub fn on_update(self) -> &'a mut crate::W<REG> {
        self.variant(Dmas::OnUpdate)
    }
}
#[doc = "Master mode control\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Mmc {
    #[doc = "0: Use UPG bit from SWEVG register"]
    Reset = 0,
    #[doc = "1: Use CEN bit from CTL0 register"]
    Enable = 1,
    #[doc = "2: Use the update event"]
    Update = 2,
    #[doc = "3: The trigger output send a positive pulse when a capture or a compare match occurred in channel 0"]
    CaptureComparePulse = 3,
    #[doc = "4: O0CPRE signal is used as trigger output"]
    CompareO0c = 4,
    #[doc = "5: O1CPRE signal is used as trigger output"]
    CompareO1c = 5,
    #[doc = "6: O2CPRE signal is used as trigger output"]
    CompareO2c = 6,
    #[doc = "7: O3CPRE signal is used as trigger output"]
    CompareO3c = 7,
}
impl From<Mmc> for u8 {
    #[inline(always)]
    fn from(variant: Mmc) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Mmc {
    type Ux = u8;
}
#[doc = "Field `MMC` reader - Master mode control"]
pub type MmcR = crate::FieldReader<Mmc>;
impl MmcR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Mmc {
        match self.bits {
            0 => Mmc::Reset,
            1 => Mmc::Enable,
            2 => Mmc::Update,
            3 => Mmc::CaptureComparePulse,
            4 => Mmc::CompareO0c,
            5 => Mmc::CompareO1c,
            6 => Mmc::CompareO2c,
            7 => Mmc::CompareO3c,
            _ => unreachable!(),
        }
    }
    #[doc = "Use UPG bit from SWEVG register"]
    #[inline(always)]
    pub fn is_reset(&self) -> bool {
        *self == Mmc::Reset
    }
    #[doc = "Use CEN bit from CTL0 register"]
    #[inline(always)]
    pub fn is_enable(&self) -> bool {
        *self == Mmc::Enable
    }
    #[doc = "Use the update event"]
    #[inline(always)]
    pub fn is_update(&self) -> bool {
        *self == Mmc::Update
    }
    #[doc = "The trigger output send a positive pulse when a capture or a compare match occurred in channel 0"]
    #[inline(always)]
    pub fn is_capture_compare_pulse(&self) -> bool {
        *self == Mmc::CaptureComparePulse
    }
    #[doc = "O0CPRE signal is used as trigger output"]
    #[inline(always)]
    pub fn is_compare_o0c(&self) -> bool {
        *self == Mmc::CompareO0c
    }
    #[doc = "O1CPRE signal is used as trigger output"]
    #[inline(always)]
    pub fn is_compare_o1c(&self) -> bool {
        *self == Mmc::CompareO1c
    }
    #[doc = "O2CPRE signal is used as trigger output"]
    #[inline(always)]
    pub fn is_compare_o2c(&self) -> bool {
        *self == Mmc::CompareO2c
    }
    #[doc = "O3CPRE signal is used as trigger output"]
    #[inline(always)]
    pub fn is_compare_o3c(&self) -> bool {
        *self == Mmc::CompareO3c
    }
}
#[doc = "Field `MMC` writer - Master mode control"]
pub type MmcW<'a, REG> = crate::FieldWriterSafe<'a, REG, 3, Mmc>;
impl<'a, REG> MmcW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Use UPG bit from SWEVG register"]
    #[inline(always)]
    pub fn reset(self) -> &'a mut crate::W<REG> {
        self.variant(Mmc::Reset)
    }
    #[doc = "Use CEN bit from CTL0 register"]
    #[inline(always)]
    pub fn enable(self) -> &'a mut crate::W<REG> {
        self.variant(Mmc::Enable)
    }
    #[doc = "Use the update event"]
    #[inline(always)]
    pub fn update(self) -> &'a mut crate::W<REG> {
        self.variant(Mmc::Update)
    }
    #[doc = "The trigger output send a positive pulse when a capture or a compare match occurred in channel 0"]
    #[inline(always)]
    pub fn capture_compare_pulse(self) -> &'a mut crate::W<REG> {
        self.variant(Mmc::CaptureComparePulse)
    }
    #[doc = "O0CPRE signal is used as trigger output"]
    #[inline(always)]
    pub fn compare_o0c(self) -> &'a mut crate::W<REG> {
        self.variant(Mmc::CompareO0c)
    }
    #[doc = "O1CPRE signal is used as trigger output"]
    #[inline(always)]
    pub fn compare_o1c(self) -> &'a mut crate::W<REG> {
        self.variant(Mmc::CompareO1c)
    }
    #[doc = "O2CPRE signal is used as trigger output"]
    #[inline(always)]
    pub fn compare_o2c(self) -> &'a mut crate::W<REG> {
        self.variant(Mmc::CompareO2c)
    }
    #[doc = "O3CPRE signal is used as trigger output"]
    #[inline(always)]
    pub fn compare_o3c(self) -> &'a mut crate::W<REG> {
        self.variant(Mmc::CompareO3c)
    }
}
#[doc = "Channel 0 trigger input selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ti0s {
    #[doc = "0: The CH0 pin input is selected as channel 0 trigger input"]
    Normal = 0,
    #[doc = "1: The XOR of CH0, CH1 and CH2 pins are selected as channel 0 trigger input"]
    Xor = 1,
}
impl From<Ti0s> for bool {
    #[inline(always)]
    fn from(variant: Ti0s) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `TI0S` reader - Channel 0 trigger input selection"]
pub type Ti0sR = crate::BitReader<Ti0s>;
impl Ti0sR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ti0s {
        match self.bits {
            false => Ti0s::Normal,
            true => Ti0s::Xor,
        }
    }
    #[doc = "The CH0 pin input is selected as channel 0 trigger input"]
    #[inline(always)]
    pub fn is_normal(&self) -> bool {
        *self == Ti0s::Normal
    }
    #[doc = "The XOR of CH0, CH1 and CH2 pins are selected as channel 0 trigger input"]
    #[inline(always)]
    pub fn is_xor(&self) -> bool {
        *self == Ti0s::Xor
    }
}
#[doc = "Field `TI0S` writer - Channel 0 trigger input selection"]
pub type Ti0sW<'a, REG> = crate::BitWriter<'a, REG, Ti0s>;
impl<'a, REG> Ti0sW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "The CH0 pin input is selected as channel 0 trigger input"]
    #[inline(always)]
    pub fn normal(self) -> &'a mut crate::W<REG> {
        self.variant(Ti0s::Normal)
    }
    #[doc = "The XOR of CH0, CH1 and CH2 pins are selected as channel 0 trigger input"]
    #[inline(always)]
    pub fn xor(self) -> &'a mut crate::W<REG> {
        self.variant(Ti0s::Xor)
    }
}
#[doc = "Idle state of channel 0 output\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Iso0 {
    #[doc = "0: CHn_O=0 (after a dead-time if CHn_ON is implemented) when POEN=0"]
    Low = 0,
    #[doc = "1: CHn_O=1 (after a dead-time if CHn_ON is implemented) when POEN=0"]
    High = 1,
}
impl From<Iso0> for bool {
    #[inline(always)]
    fn from(variant: Iso0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `ISO0` reader - Idle state of channel 0 output"]
pub type Iso0R = crate::BitReader<Iso0>;
impl Iso0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Iso0 {
        match self.bits {
            false => Iso0::Low,
            true => Iso0::High,
        }
    }
    #[doc = "CHn_O=0 (after a dead-time if CHn_ON is implemented) when POEN=0"]
    #[inline(always)]
    pub fn is_low(&self) -> bool {
        *self == Iso0::Low
    }
    #[doc = "CHn_O=1 (after a dead-time if CHn_ON is implemented) when POEN=0"]
    #[inline(always)]
    pub fn is_high(&self) -> bool {
        *self == Iso0::High
    }
}
#[doc = "Field `ISO0` writer - Idle state of channel 0 output"]
pub type Iso0W<'a, REG> = crate::BitWriter<'a, REG, Iso0>;
impl<'a, REG> Iso0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "CHn_O=0 (after a dead-time if CHn_ON is implemented) when POEN=0"]
    #[inline(always)]
    pub fn low(self) -> &'a mut crate::W<REG> {
        self.variant(Iso0::Low)
    }
    #[doc = "CHn_O=1 (after a dead-time if CHn_ON is implemented) when POEN=0"]
    #[inline(always)]
    pub fn high(self) -> &'a mut crate::W<REG> {
        self.variant(Iso0::High)
    }
}
#[doc = "Idle state of channel 0 complementary output\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Iso0n {
    #[doc = "0: CHn_ON=0 when POEN=0"]
    Low = 0,
    #[doc = "1: CHn_ON=1 when POEN=0"]
    High = 1,
}
impl From<Iso0n> for bool {
    #[inline(always)]
    fn from(variant: Iso0n) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `ISO0N` reader - Idle state of channel 0 complementary output"]
pub type Iso0nR = crate::BitReader<Iso0n>;
impl Iso0nR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Iso0n {
        match self.bits {
            false => Iso0n::Low,
            true => Iso0n::High,
        }
    }
    #[doc = "CHn_ON=0 when POEN=0"]
    #[inline(always)]
    pub fn is_low(&self) -> bool {
        *self == Iso0n::Low
    }
    #[doc = "CHn_ON=1 when POEN=0"]
    #[inline(always)]
    pub fn is_high(&self) -> bool {
        *self == Iso0n::High
    }
}
#[doc = "Field `ISO0N` writer - Idle state of channel 0 complementary output"]
pub type Iso0nW<'a, REG> = crate::BitWriter<'a, REG, Iso0n>;
impl<'a, REG> Iso0nW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "CHn_ON=0 when POEN=0"]
    #[inline(always)]
    pub fn low(self) -> &'a mut crate::W<REG> {
        self.variant(Iso0n::Low)
    }
    #[doc = "CHn_ON=1 when POEN=0"]
    #[inline(always)]
    pub fn high(self) -> &'a mut crate::W<REG> {
        self.variant(Iso0n::High)
    }
}
#[doc = "Field `ISO1` reader - Idle state of channel 1 output"]
pub use Iso0R as Iso1R;
#[doc = "Field `ISO2` reader - Idle state of channel 2 output"]
pub use Iso0R as Iso2R;
#[doc = "Field `ISO3` reader - Idle state of channel 3 output"]
pub use Iso0R as Iso3R;
#[doc = "Field `ISO1` writer - Idle state of channel 1 output"]
pub use Iso0W as Iso1W;
#[doc = "Field `ISO2` writer - Idle state of channel 2 output"]
pub use Iso0W as Iso2W;
#[doc = "Field `ISO3` writer - Idle state of channel 3 output"]
pub use Iso0W as Iso3W;
#[doc = "Field `ISO1N` reader - Idle state of channel 1 complementary output"]
pub use Iso0nR as Iso1nR;
#[doc = "Field `ISO2N` reader - Idle state of channel 2 complementary output"]
pub use Iso0nR as Iso2nR;
#[doc = "Field `ISO1N` writer - Idle state of channel 1 complementary output"]
pub use Iso0nW as Iso1nW;
#[doc = "Field `ISO2N` writer - Idle state of channel 2 complementary output"]
pub use Iso0nW as Iso2nW;
impl R {
    #[doc = "Bit 0 - Commutation control shadow enable"]
    #[inline(always)]
    pub fn ccse(&self) -> CcseR {
        CcseR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 2 - Commutation control shadow register update control"]
    #[inline(always)]
    pub fn ccuc(&self) -> CcucR {
        CcucR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - DMA request source selection"]
    #[inline(always)]
    pub fn dmas(&self) -> DmasR {
        DmasR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:6 - Master mode control"]
    #[inline(always)]
    pub fn mmc(&self) -> MmcR {
        MmcR::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bit 7 - Channel 0 trigger input selection"]
    #[inline(always)]
    pub fn ti0s(&self) -> Ti0sR {
        Ti0sR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Idle state of channel 0 output"]
    #[inline(always)]
    pub fn iso0(&self) -> Iso0R {
        Iso0R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Idle state of channel 0 complementary output"]
    #[inline(always)]
    pub fn iso0n(&self) -> Iso0nR {
        Iso0nR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Idle state of channel 1 output"]
    #[inline(always)]
    pub fn iso1(&self) -> Iso1R {
        Iso1R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Idle state of channel 1 complementary output"]
    #[inline(always)]
    pub fn iso1n(&self) -> Iso1nR {
        Iso1nR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Idle state of channel 2 output"]
    #[inline(always)]
    pub fn iso2(&self) -> Iso2R {
        Iso2R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Idle state of channel 2 complementary output"]
    #[inline(always)]
    pub fn iso2n(&self) -> Iso2nR {
        Iso2nR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Idle state of channel 3 output"]
    #[inline(always)]
    pub fn iso3(&self) -> Iso3R {
        Iso3R::new(((self.bits >> 14) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Commutation control shadow enable"]
    #[inline(always)]
    #[must_use]
    pub fn ccse(&mut self) -> CcseW<Ctl1Spec> {
        CcseW::new(self, 0)
    }
    #[doc = "Bit 2 - Commutation control shadow register update control"]
    #[inline(always)]
    #[must_use]
    pub fn ccuc(&mut self) -> CcucW<Ctl1Spec> {
        CcucW::new(self, 2)
    }
    #[doc = "Bit 3 - DMA request source selection"]
    #[inline(always)]
    #[must_use]
    pub fn dmas(&mut self) -> DmasW<Ctl1Spec> {
        DmasW::new(self, 3)
    }
    #[doc = "Bits 4:6 - Master mode control"]
    #[inline(always)]
    #[must_use]
    pub fn mmc(&mut self) -> MmcW<Ctl1Spec> {
        MmcW::new(self, 4)
    }
    #[doc = "Bit 7 - Channel 0 trigger input selection"]
    #[inline(always)]
    #[must_use]
    pub fn ti0s(&mut self) -> Ti0sW<Ctl1Spec> {
        Ti0sW::new(self, 7)
    }
    #[doc = "Bit 8 - Idle state of channel 0 output"]
    #[inline(always)]
    #[must_use]
    pub fn iso0(&mut self) -> Iso0W<Ctl1Spec> {
        Iso0W::new(self, 8)
    }
    #[doc = "Bit 9 - Idle state of channel 0 complementary output"]
    #[inline(always)]
    #[must_use]
    pub fn iso0n(&mut self) -> Iso0nW<Ctl1Spec> {
        Iso0nW::new(self, 9)
    }
    #[doc = "Bit 10 - Idle state of channel 1 output"]
    #[inline(always)]
    #[must_use]
    pub fn iso1(&mut self) -> Iso1W<Ctl1Spec> {
        Iso1W::new(self, 10)
    }
    #[doc = "Bit 11 - Idle state of channel 1 complementary output"]
    #[inline(always)]
    #[must_use]
    pub fn iso1n(&mut self) -> Iso1nW<Ctl1Spec> {
        Iso1nW::new(self, 11)
    }
    #[doc = "Bit 12 - Idle state of channel 2 output"]
    #[inline(always)]
    #[must_use]
    pub fn iso2(&mut self) -> Iso2W<Ctl1Spec> {
        Iso2W::new(self, 12)
    }
    #[doc = "Bit 13 - Idle state of channel 2 complementary output"]
    #[inline(always)]
    #[must_use]
    pub fn iso2n(&mut self) -> Iso2nW<Ctl1Spec> {
        Iso2nW::new(self, 13)
    }
    #[doc = "Bit 14 - Idle state of channel 3 output"]
    #[inline(always)]
    #[must_use]
    pub fn iso3(&mut self) -> Iso3W<Ctl1Spec> {
        Iso3W::new(self, 14)
    }
}
#[doc = "control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
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
