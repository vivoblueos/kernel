#[doc = "Register `CCHP` reader"]
pub type R = crate::R<CchpSpec>;
#[doc = "Register `CCHP` writer"]
pub type W = crate::W<CchpSpec>;
#[doc = "Field `DTCFG` reader - Dead time configure"]
pub type DtcfgR = crate::FieldReader;
#[doc = "Field `DTCFG` writer - Dead time configure"]
pub type DtcfgW<'a, REG> = crate::FieldWriterSafe<'a, REG, 8>;
#[doc = "Complementary register protect control\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Prot {
    #[doc = "0: Write protection disabled"]
    Disabled = 0,
    #[doc = "1: Protection mode 0"]
    Mode0 = 1,
    #[doc = "2: Protection mode 1"]
    Mode1 = 2,
    #[doc = "3: Protection mode 2"]
    Mode2 = 3,
}
impl From<Prot> for u8 {
    #[inline(always)]
    fn from(variant: Prot) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Prot {
    type Ux = u8;
}
#[doc = "Field `PROT` reader - Complementary register protect control"]
pub type ProtR = crate::FieldReader<Prot>;
impl ProtR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Prot {
        match self.bits {
            0 => Prot::Disabled,
            1 => Prot::Mode0,
            2 => Prot::Mode1,
            3 => Prot::Mode2,
            _ => unreachable!(),
        }
    }
    #[doc = "Write protection disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Prot::Disabled
    }
    #[doc = "Protection mode 0"]
    #[inline(always)]
    pub fn is_mode0(&self) -> bool {
        *self == Prot::Mode0
    }
    #[doc = "Protection mode 1"]
    #[inline(always)]
    pub fn is_mode1(&self) -> bool {
        *self == Prot::Mode1
    }
    #[doc = "Protection mode 2"]
    #[inline(always)]
    pub fn is_mode2(&self) -> bool {
        *self == Prot::Mode2
    }
}
#[doc = "Field `PROT` writer - Complementary register protect control"]
pub type ProtW<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, Prot>;
impl<'a, REG> ProtW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Write protection disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Prot::Disabled)
    }
    #[doc = "Protection mode 0"]
    #[inline(always)]
    pub fn mode0(self) -> &'a mut crate::W<REG> {
        self.variant(Prot::Mode0)
    }
    #[doc = "Protection mode 1"]
    #[inline(always)]
    pub fn mode1(self) -> &'a mut crate::W<REG> {
        self.variant(Prot::Mode1)
    }
    #[doc = "Protection mode 2"]
    #[inline(always)]
    pub fn mode2(self) -> &'a mut crate::W<REG> {
        self.variant(Prot::Mode2)
    }
}
#[doc = "Idle mode off-state configure\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ios {
    #[doc = "0: When POEN is reset, the channel output signals are disabled"]
    Disabled = 0,
    #[doc = "1: When POEN is reset, the channel output signals are enabled"]
    Enabled = 1,
}
impl From<Ios> for bool {
    #[inline(always)]
    fn from(variant: Ios) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `IOS` reader - Idle mode off-state configure"]
pub type IosR = crate::BitReader<Ios>;
impl IosR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ios {
        match self.bits {
            false => Ios::Disabled,
            true => Ios::Enabled,
        }
    }
    #[doc = "When POEN is reset, the channel output signals are disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Ios::Disabled
    }
    #[doc = "When POEN is reset, the channel output signals are enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Ios::Enabled
    }
}
#[doc = "Field `IOS` writer - Idle mode off-state configure"]
pub type IosW<'a, REG> = crate::BitWriter<'a, REG, Ios>;
impl<'a, REG> IosW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "When POEN is reset, the channel output signals are disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ios::Disabled)
    }
    #[doc = "When POEN is reset, the channel output signals are enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ios::Enabled)
    }
}
#[doc = "Run mode off-state configure\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ros {
    #[doc = "0: When POEN is set, the channel output signals are disabled"]
    Disabled = 0,
    #[doc = "1: When POEN is set, the channel output signals are enabled"]
    Enabled = 1,
}
impl From<Ros> for bool {
    #[inline(always)]
    fn from(variant: Ros) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `ROS` reader - Run mode off-state configure"]
pub type RosR = crate::BitReader<Ros>;
impl RosR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ros {
        match self.bits {
            false => Ros::Disabled,
            true => Ros::Enabled,
        }
    }
    #[doc = "When POEN is set, the channel output signals are disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Ros::Disabled
    }
    #[doc = "When POEN is set, the channel output signals are enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Ros::Enabled
    }
}
#[doc = "Field `ROS` writer - Run mode off-state configure"]
pub type RosW<'a, REG> = crate::BitWriter<'a, REG, Ros>;
impl<'a, REG> RosW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "When POEN is set, the channel output signals are disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ros::Disabled)
    }
    #[doc = "When POEN is set, the channel output signals are enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ros::Enabled)
    }
}
#[doc = "Break enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Brken {
    #[doc = "0: Break inputs disabled"]
    Disabled = 0,
    #[doc = "1: Break inputs enabled"]
    Enabled = 1,
}
impl From<Brken> for bool {
    #[inline(always)]
    fn from(variant: Brken) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `BRKEN` reader - Break enable"]
pub type BrkenR = crate::BitReader<Brken>;
impl BrkenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Brken {
        match self.bits {
            false => Brken::Disabled,
            true => Brken::Enabled,
        }
    }
    #[doc = "Break inputs disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Brken::Disabled
    }
    #[doc = "Break inputs enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Brken::Enabled
    }
}
#[doc = "Field `BRKEN` writer - Break enable"]
pub type BrkenW<'a, REG> = crate::BitWriter<'a, REG, Brken>;
impl<'a, REG> BrkenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Break inputs disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Brken::Disabled)
    }
    #[doc = "Break inputs enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Brken::Enabled)
    }
}
#[doc = "Break polarity\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Brkp {
    #[doc = "0: BRKIN is active low"]
    Inverted = 0,
    #[doc = "1: BRKIN is active high"]
    NotInverted = 1,
}
impl From<Brkp> for bool {
    #[inline(always)]
    fn from(variant: Brkp) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `BRKP` reader - Break polarity"]
pub type BrkpR = crate::BitReader<Brkp>;
impl BrkpR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Brkp {
        match self.bits {
            false => Brkp::Inverted,
            true => Brkp::NotInverted,
        }
    }
    #[doc = "BRKIN is active low"]
    #[inline(always)]
    pub fn is_inverted(&self) -> bool {
        *self == Brkp::Inverted
    }
    #[doc = "BRKIN is active high"]
    #[inline(always)]
    pub fn is_not_inverted(&self) -> bool {
        *self == Brkp::NotInverted
    }
}
#[doc = "Field `BRKP` writer - Break polarity"]
pub type BrkpW<'a, REG> = crate::BitWriter<'a, REG, Brkp>;
impl<'a, REG> BrkpW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "BRKIN is active low"]
    #[inline(always)]
    pub fn inverted(self) -> &'a mut crate::W<REG> {
        self.variant(Brkp::Inverted)
    }
    #[doc = "BRKIN is active high"]
    #[inline(always)]
    pub fn not_inverted(self) -> &'a mut crate::W<REG> {
        self.variant(Brkp::NotInverted)
    }
}
#[doc = "Output automatic enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Oaen {
    #[doc = "0: POEN cannot be set by hardware"]
    Manual = 0,
    #[doc = "1: POEN can be set by hardware automatically at the next update event"]
    Automatic = 1,
}
impl From<Oaen> for bool {
    #[inline(always)]
    fn from(variant: Oaen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `OAEN` reader - Output automatic enable"]
pub type OaenR = crate::BitReader<Oaen>;
impl OaenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Oaen {
        match self.bits {
            false => Oaen::Manual,
            true => Oaen::Automatic,
        }
    }
    #[doc = "POEN cannot be set by hardware"]
    #[inline(always)]
    pub fn is_manual(&self) -> bool {
        *self == Oaen::Manual
    }
    #[doc = "POEN can be set by hardware automatically at the next update event"]
    #[inline(always)]
    pub fn is_automatic(&self) -> bool {
        *self == Oaen::Automatic
    }
}
#[doc = "Field `OAEN` writer - Output automatic enable"]
pub type OaenW<'a, REG> = crate::BitWriter<'a, REG, Oaen>;
impl<'a, REG> OaenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "POEN cannot be set by hardware"]
    #[inline(always)]
    pub fn manual(self) -> &'a mut crate::W<REG> {
        self.variant(Oaen::Manual)
    }
    #[doc = "POEN can be set by hardware automatically at the next update event"]
    #[inline(always)]
    pub fn automatic(self) -> &'a mut crate::W<REG> {
        self.variant(Oaen::Automatic)
    }
}
#[doc = "Primary output enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Poen {
    #[doc = "0: Channel outputs are disabled"]
    Disabled = 0,
    #[doc = "1: Channel outputs are enabled"]
    Enabled = 1,
}
impl From<Poen> for bool {
    #[inline(always)]
    fn from(variant: Poen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `POEN` reader - Primary output enable"]
pub type PoenR = crate::BitReader<Poen>;
impl PoenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Poen {
        match self.bits {
            false => Poen::Disabled,
            true => Poen::Enabled,
        }
    }
    #[doc = "Channel outputs are disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Poen::Disabled
    }
    #[doc = "Channel outputs are enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Poen::Enabled
    }
}
#[doc = "Field `POEN` writer - Primary output enable"]
pub type PoenW<'a, REG> = crate::BitWriter<'a, REG, Poen>;
impl<'a, REG> PoenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Channel outputs are disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Poen::Disabled)
    }
    #[doc = "Channel outputs are enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Poen::Enabled)
    }
}
impl R {
    #[doc = "Bits 0:7 - Dead time configure"]
    #[inline(always)]
    pub fn dtcfg(&self) -> DtcfgR {
        DtcfgR::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:9 - Complementary register protect control"]
    #[inline(always)]
    pub fn prot(&self) -> ProtR {
        ProtR::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bit 10 - Idle mode off-state configure"]
    #[inline(always)]
    pub fn ios(&self) -> IosR {
        IosR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Run mode off-state configure"]
    #[inline(always)]
    pub fn ros(&self) -> RosR {
        RosR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Break enable"]
    #[inline(always)]
    pub fn brken(&self) -> BrkenR {
        BrkenR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Break polarity"]
    #[inline(always)]
    pub fn brkp(&self) -> BrkpR {
        BrkpR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Output automatic enable"]
    #[inline(always)]
    pub fn oaen(&self) -> OaenR {
        OaenR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Primary output enable"]
    #[inline(always)]
    pub fn poen(&self) -> PoenR {
        PoenR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:7 - Dead time configure"]
    #[inline(always)]
    #[must_use]
    pub fn dtcfg(&mut self) -> DtcfgW<CchpSpec> {
        DtcfgW::new(self, 0)
    }
    #[doc = "Bits 8:9 - Complementary register protect control"]
    #[inline(always)]
    #[must_use]
    pub fn prot(&mut self) -> ProtW<CchpSpec> {
        ProtW::new(self, 8)
    }
    #[doc = "Bit 10 - Idle mode off-state configure"]
    #[inline(always)]
    #[must_use]
    pub fn ios(&mut self) -> IosW<CchpSpec> {
        IosW::new(self, 10)
    }
    #[doc = "Bit 11 - Run mode off-state configure"]
    #[inline(always)]
    #[must_use]
    pub fn ros(&mut self) -> RosW<CchpSpec> {
        RosW::new(self, 11)
    }
    #[doc = "Bit 12 - Break enable"]
    #[inline(always)]
    #[must_use]
    pub fn brken(&mut self) -> BrkenW<CchpSpec> {
        BrkenW::new(self, 12)
    }
    #[doc = "Bit 13 - Break polarity"]
    #[inline(always)]
    #[must_use]
    pub fn brkp(&mut self) -> BrkpW<CchpSpec> {
        BrkpW::new(self, 13)
    }
    #[doc = "Bit 14 - Output automatic enable"]
    #[inline(always)]
    #[must_use]
    pub fn oaen(&mut self) -> OaenW<CchpSpec> {
        OaenW::new(self, 14)
    }
    #[doc = "Bit 15 - Primary output enable"]
    #[inline(always)]
    #[must_use]
    pub fn poen(&mut self) -> PoenW<CchpSpec> {
        PoenW::new(self, 15)
    }
}
#[doc = "channel complementary protection register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cchp::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cchp::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CchpSpec;
impl crate::RegisterSpec for CchpSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cchp::R`](R) reader structure"]
impl crate::Readable for CchpSpec {}
#[doc = "`write(|w| ..)` method takes [`cchp::W`](W) writer structure"]
impl crate::Writable for CchpSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CCHP to value 0"]
impl crate::Resettable for CchpSpec {
    const RESET_VALUE: u32 = 0;
}
