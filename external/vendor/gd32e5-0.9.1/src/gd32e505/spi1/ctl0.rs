#[doc = "Register `CTL0` reader"]
pub type R = crate::R<Ctl0Spec>;
#[doc = "Register `CTL0` writer"]
pub type W = crate::W<Ctl0Spec>;
#[doc = "Clock Phase Selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ckph {
    #[doc = "0: The first clock transition is the first data capture edge"]
    FirstEdge = 0,
    #[doc = "1: The second clock transition is the first data capture edge"]
    SecondEdge = 1,
}
impl From<Ckph> for bool {
    #[inline(always)]
    fn from(variant: Ckph) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CKPH` reader - Clock Phase Selection"]
pub type CkphR = crate::BitReader<Ckph>;
impl CkphR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ckph {
        match self.bits {
            false => Ckph::FirstEdge,
            true => Ckph::SecondEdge,
        }
    }
    #[doc = "The first clock transition is the first data capture edge"]
    #[inline(always)]
    pub fn is_first_edge(&self) -> bool {
        *self == Ckph::FirstEdge
    }
    #[doc = "The second clock transition is the first data capture edge"]
    #[inline(always)]
    pub fn is_second_edge(&self) -> bool {
        *self == Ckph::SecondEdge
    }
}
#[doc = "Field `CKPH` writer - Clock Phase Selection"]
pub type CkphW<'a, REG> = crate::BitWriter<'a, REG, Ckph>;
impl<'a, REG> CkphW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "The first clock transition is the first data capture edge"]
    #[inline(always)]
    pub fn first_edge(self) -> &'a mut crate::W<REG> {
        self.variant(Ckph::FirstEdge)
    }
    #[doc = "The second clock transition is the first data capture edge"]
    #[inline(always)]
    pub fn second_edge(self) -> &'a mut crate::W<REG> {
        self.variant(Ckph::SecondEdge)
    }
}
#[doc = "Clock polarity Selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ckpl {
    #[doc = "0: CLK pulled low when idle"]
    IdleLow = 0,
    #[doc = "1: CLK pulled high when idle"]
    IdleHigh = 1,
}
impl From<Ckpl> for bool {
    #[inline(always)]
    fn from(variant: Ckpl) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CKPL` reader - Clock polarity Selection"]
pub type CkplR = crate::BitReader<Ckpl>;
impl CkplR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ckpl {
        match self.bits {
            false => Ckpl::IdleLow,
            true => Ckpl::IdleHigh,
        }
    }
    #[doc = "CLK pulled low when idle"]
    #[inline(always)]
    pub fn is_idle_low(&self) -> bool {
        *self == Ckpl::IdleLow
    }
    #[doc = "CLK pulled high when idle"]
    #[inline(always)]
    pub fn is_idle_high(&self) -> bool {
        *self == Ckpl::IdleHigh
    }
}
#[doc = "Field `CKPL` writer - Clock polarity Selection"]
pub type CkplW<'a, REG> = crate::BitWriter<'a, REG, Ckpl>;
impl<'a, REG> CkplW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "CLK pulled low when idle"]
    #[inline(always)]
    pub fn idle_low(self) -> &'a mut crate::W<REG> {
        self.variant(Ckpl::IdleLow)
    }
    #[doc = "CLK pulled high when idle"]
    #[inline(always)]
    pub fn idle_high(self) -> &'a mut crate::W<REG> {
        self.variant(Ckpl::IdleHigh)
    }
}
#[doc = "Master Mode Enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mstmod {
    #[doc = "0: Slave configuration"]
    Slave = 0,
    #[doc = "1: Master configuration"]
    Master = 1,
}
impl From<Mstmod> for bool {
    #[inline(always)]
    fn from(variant: Mstmod) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `MSTMOD` reader - Master Mode Enable"]
pub type MstmodR = crate::BitReader<Mstmod>;
impl MstmodR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Mstmod {
        match self.bits {
            false => Mstmod::Slave,
            true => Mstmod::Master,
        }
    }
    #[doc = "Slave configuration"]
    #[inline(always)]
    pub fn is_slave(&self) -> bool {
        *self == Mstmod::Slave
    }
    #[doc = "Master configuration"]
    #[inline(always)]
    pub fn is_master(&self) -> bool {
        *self == Mstmod::Master
    }
}
#[doc = "Field `MSTMOD` writer - Master Mode Enable"]
pub type MstmodW<'a, REG> = crate::BitWriter<'a, REG, Mstmod>;
impl<'a, REG> MstmodW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Slave configuration"]
    #[inline(always)]
    pub fn slave(self) -> &'a mut crate::W<REG> {
        self.variant(Mstmod::Slave)
    }
    #[doc = "Master configuration"]
    #[inline(always)]
    pub fn master(self) -> &'a mut crate::W<REG> {
        self.variant(Mstmod::Master)
    }
}
#[doc = "Master Clock Prescaler Selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Psc {
    #[doc = "0: PCLK / 2"]
    Div2 = 0,
    #[doc = "1: PCLK / 4"]
    Div4 = 1,
    #[doc = "2: PCLK / 8"]
    Div8 = 2,
    #[doc = "3: PCLK / 16"]
    Div16 = 3,
    #[doc = "4: PCLK / 32"]
    Div32 = 4,
    #[doc = "5: PCLK / 64"]
    Div64 = 5,
    #[doc = "6: PCLK / 128"]
    Div128 = 6,
    #[doc = "7: PCLK / 256"]
    Div256 = 7,
}
impl From<Psc> for u8 {
    #[inline(always)]
    fn from(variant: Psc) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Psc {
    type Ux = u8;
}
#[doc = "Field `PSC` reader - Master Clock Prescaler Selection"]
pub type PscR = crate::FieldReader<Psc>;
impl PscR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Psc {
        match self.bits {
            0 => Psc::Div2,
            1 => Psc::Div4,
            2 => Psc::Div8,
            3 => Psc::Div16,
            4 => Psc::Div32,
            5 => Psc::Div64,
            6 => Psc::Div128,
            7 => Psc::Div256,
            _ => unreachable!(),
        }
    }
    #[doc = "PCLK / 2"]
    #[inline(always)]
    pub fn is_div2(&self) -> bool {
        *self == Psc::Div2
    }
    #[doc = "PCLK / 4"]
    #[inline(always)]
    pub fn is_div4(&self) -> bool {
        *self == Psc::Div4
    }
    #[doc = "PCLK / 8"]
    #[inline(always)]
    pub fn is_div8(&self) -> bool {
        *self == Psc::Div8
    }
    #[doc = "PCLK / 16"]
    #[inline(always)]
    pub fn is_div16(&self) -> bool {
        *self == Psc::Div16
    }
    #[doc = "PCLK / 32"]
    #[inline(always)]
    pub fn is_div32(&self) -> bool {
        *self == Psc::Div32
    }
    #[doc = "PCLK / 64"]
    #[inline(always)]
    pub fn is_div64(&self) -> bool {
        *self == Psc::Div64
    }
    #[doc = "PCLK / 128"]
    #[inline(always)]
    pub fn is_div128(&self) -> bool {
        *self == Psc::Div128
    }
    #[doc = "PCLK / 256"]
    #[inline(always)]
    pub fn is_div256(&self) -> bool {
        *self == Psc::Div256
    }
}
#[doc = "Field `PSC` writer - Master Clock Prescaler Selection"]
pub type PscW<'a, REG> = crate::FieldWriterSafe<'a, REG, 3, Psc>;
impl<'a, REG> PscW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "PCLK / 2"]
    #[inline(always)]
    pub fn div2(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::Div2)
    }
    #[doc = "PCLK / 4"]
    #[inline(always)]
    pub fn div4(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::Div4)
    }
    #[doc = "PCLK / 8"]
    #[inline(always)]
    pub fn div8(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::Div8)
    }
    #[doc = "PCLK / 16"]
    #[inline(always)]
    pub fn div16(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::Div16)
    }
    #[doc = "PCLK / 32"]
    #[inline(always)]
    pub fn div32(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::Div32)
    }
    #[doc = "PCLK / 64"]
    #[inline(always)]
    pub fn div64(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::Div64)
    }
    #[doc = "PCLK / 128"]
    #[inline(always)]
    pub fn div128(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::Div128)
    }
    #[doc = "PCLK / 256"]
    #[inline(always)]
    pub fn div256(self) -> &'a mut crate::W<REG> {
        self.variant(Psc::Div256)
    }
}
#[doc = "SPI enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Spien {
    #[doc = "0: Peripheral disabled"]
    Disabled = 0,
    #[doc = "1: Peripheral enabled"]
    Enabled = 1,
}
impl From<Spien> for bool {
    #[inline(always)]
    fn from(variant: Spien) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `SPIEN` reader - SPI enable"]
pub type SpienR = crate::BitReader<Spien>;
impl SpienR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Spien {
        match self.bits {
            false => Spien::Disabled,
            true => Spien::Enabled,
        }
    }
    #[doc = "Peripheral disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Spien::Disabled
    }
    #[doc = "Peripheral enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Spien::Enabled
    }
}
#[doc = "Field `SPIEN` writer - SPI enable"]
pub type SpienW<'a, REG> = crate::BitWriter<'a, REG, Spien>;
impl<'a, REG> SpienW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Peripheral disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Spien::Disabled)
    }
    #[doc = "Peripheral enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Spien::Enabled)
    }
}
#[doc = "LSB First Mode\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lf {
    #[doc = "0: Data is transmitted/received with the MSB first"]
    Msbfirst = 0,
    #[doc = "1: Data is transmitted/received with the LSB first"]
    Lsbfirst = 1,
}
impl From<Lf> for bool {
    #[inline(always)]
    fn from(variant: Lf) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `LF` reader - LSB First Mode"]
pub type LfR = crate::BitReader<Lf>;
impl LfR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Lf {
        match self.bits {
            false => Lf::Msbfirst,
            true => Lf::Lsbfirst,
        }
    }
    #[doc = "Data is transmitted/received with the MSB first"]
    #[inline(always)]
    pub fn is_msbfirst(&self) -> bool {
        *self == Lf::Msbfirst
    }
    #[doc = "Data is transmitted/received with the LSB first"]
    #[inline(always)]
    pub fn is_lsbfirst(&self) -> bool {
        *self == Lf::Lsbfirst
    }
}
#[doc = "Field `LF` writer - LSB First Mode"]
pub type LfW<'a, REG> = crate::BitWriter<'a, REG, Lf>;
impl<'a, REG> LfW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Data is transmitted/received with the MSB first"]
    #[inline(always)]
    pub fn msbfirst(self) -> &'a mut crate::W<REG> {
        self.variant(Lf::Msbfirst)
    }
    #[doc = "Data is transmitted/received with the LSB first"]
    #[inline(always)]
    pub fn lsbfirst(self) -> &'a mut crate::W<REG> {
        self.variant(Lf::Lsbfirst)
    }
}
#[doc = "NSS Pin Selection In NSS Software Mode\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Swnss {
    #[doc = "0: NSS is pulled low"]
    SlaveSelected = 0,
    #[doc = "1: NSS is pulled high"]
    SlaveNotSelected = 1,
}
impl From<Swnss> for bool {
    #[inline(always)]
    fn from(variant: Swnss) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `SWNSS` reader - NSS Pin Selection In NSS Software Mode"]
pub type SwnssR = crate::BitReader<Swnss>;
impl SwnssR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Swnss {
        match self.bits {
            false => Swnss::SlaveSelected,
            true => Swnss::SlaveNotSelected,
        }
    }
    #[doc = "NSS is pulled low"]
    #[inline(always)]
    pub fn is_slave_selected(&self) -> bool {
        *self == Swnss::SlaveSelected
    }
    #[doc = "NSS is pulled high"]
    #[inline(always)]
    pub fn is_slave_not_selected(&self) -> bool {
        *self == Swnss::SlaveNotSelected
    }
}
#[doc = "Field `SWNSS` writer - NSS Pin Selection In NSS Software Mode"]
pub type SwnssW<'a, REG> = crate::BitWriter<'a, REG, Swnss>;
impl<'a, REG> SwnssW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "NSS is pulled low"]
    #[inline(always)]
    pub fn slave_selected(self) -> &'a mut crate::W<REG> {
        self.variant(Swnss::SlaveSelected)
    }
    #[doc = "NSS is pulled high"]
    #[inline(always)]
    pub fn slave_not_selected(self) -> &'a mut crate::W<REG> {
        self.variant(Swnss::SlaveNotSelected)
    }
}
#[doc = "NSS Software Mode Selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Swnssen {
    #[doc = "0: Software slave management disabled"]
    Hardware = 0,
    #[doc = "1: Software slave management enabled"]
    Software = 1,
}
impl From<Swnssen> for bool {
    #[inline(always)]
    fn from(variant: Swnssen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `SWNSSEN` reader - NSS Software Mode Selection"]
pub type SwnssenR = crate::BitReader<Swnssen>;
impl SwnssenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Swnssen {
        match self.bits {
            false => Swnssen::Hardware,
            true => Swnssen::Software,
        }
    }
    #[doc = "Software slave management disabled"]
    #[inline(always)]
    pub fn is_hardware(&self) -> bool {
        *self == Swnssen::Hardware
    }
    #[doc = "Software slave management enabled"]
    #[inline(always)]
    pub fn is_software(&self) -> bool {
        *self == Swnssen::Software
    }
}
#[doc = "Field `SWNSSEN` writer - NSS Software Mode Selection"]
pub type SwnssenW<'a, REG> = crate::BitWriter<'a, REG, Swnssen>;
impl<'a, REG> SwnssenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Software slave management disabled"]
    #[inline(always)]
    pub fn hardware(self) -> &'a mut crate::W<REG> {
        self.variant(Swnssen::Hardware)
    }
    #[doc = "Software slave management enabled"]
    #[inline(always)]
    pub fn software(self) -> &'a mut crate::W<REG> {
        self.variant(Swnssen::Software)
    }
}
#[doc = "Receive only\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ro {
    #[doc = "0: Full duplex (Transmit and receive)"]
    FullDuplex = 0,
    #[doc = "1: Output disabled (Receive-only mode)"]
    ReceiveOnly = 1,
}
impl From<Ro> for bool {
    #[inline(always)]
    fn from(variant: Ro) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `RO` reader - Receive only"]
pub type RoR = crate::BitReader<Ro>;
impl RoR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ro {
        match self.bits {
            false => Ro::FullDuplex,
            true => Ro::ReceiveOnly,
        }
    }
    #[doc = "Full duplex (Transmit and receive)"]
    #[inline(always)]
    pub fn is_full_duplex(&self) -> bool {
        *self == Ro::FullDuplex
    }
    #[doc = "Output disabled (Receive-only mode)"]
    #[inline(always)]
    pub fn is_receive_only(&self) -> bool {
        *self == Ro::ReceiveOnly
    }
}
#[doc = "Field `RO` writer - Receive only"]
pub type RoW<'a, REG> = crate::BitWriter<'a, REG, Ro>;
impl<'a, REG> RoW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Full duplex (Transmit and receive)"]
    #[inline(always)]
    pub fn full_duplex(self) -> &'a mut crate::W<REG> {
        self.variant(Ro::FullDuplex)
    }
    #[doc = "Output disabled (Receive-only mode)"]
    #[inline(always)]
    pub fn receive_only(self) -> &'a mut crate::W<REG> {
        self.variant(Ro::ReceiveOnly)
    }
}
#[doc = "Data frame format\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ff16 {
    #[doc = "0: 8-bit data frame format is selected for transmission/reception"]
    EightBit = 0,
    #[doc = "1: 16-bit data frame format is selected for transmission/reception"]
    SixteenBit = 1,
}
impl From<Ff16> for bool {
    #[inline(always)]
    fn from(variant: Ff16) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `FF16` reader - Data frame format"]
pub type Ff16R = crate::BitReader<Ff16>;
impl Ff16R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ff16 {
        match self.bits {
            false => Ff16::EightBit,
            true => Ff16::SixteenBit,
        }
    }
    #[doc = "8-bit data frame format is selected for transmission/reception"]
    #[inline(always)]
    pub fn is_eight_bit(&self) -> bool {
        *self == Ff16::EightBit
    }
    #[doc = "16-bit data frame format is selected for transmission/reception"]
    #[inline(always)]
    pub fn is_sixteen_bit(&self) -> bool {
        *self == Ff16::SixteenBit
    }
}
#[doc = "Field `FF16` writer - Data frame format"]
pub type Ff16W<'a, REG> = crate::BitWriter<'a, REG, Ff16>;
impl<'a, REG> Ff16W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "8-bit data frame format is selected for transmission/reception"]
    #[inline(always)]
    pub fn eight_bit(self) -> &'a mut crate::W<REG> {
        self.variant(Ff16::EightBit)
    }
    #[doc = "16-bit data frame format is selected for transmission/reception"]
    #[inline(always)]
    pub fn sixteen_bit(self) -> &'a mut crate::W<REG> {
        self.variant(Ff16::SixteenBit)
    }
}
#[doc = "CRC Next Transfer\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Crcnt {
    #[doc = "0: Next transmit value is data from Tx buffer"]
    Data = 0,
    #[doc = "1: Next transmit value is CRC value from TCRC"]
    Crc = 1,
}
impl From<Crcnt> for bool {
    #[inline(always)]
    fn from(variant: Crcnt) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CRCNT` reader - CRC Next Transfer"]
pub type CrcntR = crate::BitReader<Crcnt>;
impl CrcntR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Crcnt {
        match self.bits {
            false => Crcnt::Data,
            true => Crcnt::Crc,
        }
    }
    #[doc = "Next transmit value is data from Tx buffer"]
    #[inline(always)]
    pub fn is_data(&self) -> bool {
        *self == Crcnt::Data
    }
    #[doc = "Next transmit value is CRC value from TCRC"]
    #[inline(always)]
    pub fn is_crc(&self) -> bool {
        *self == Crcnt::Crc
    }
}
#[doc = "Field `CRCNT` writer - CRC Next Transfer"]
pub type CrcntW<'a, REG> = crate::BitWriter<'a, REG, Crcnt>;
impl<'a, REG> CrcntW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Next transmit value is data from Tx buffer"]
    #[inline(always)]
    pub fn data(self) -> &'a mut crate::W<REG> {
        self.variant(Crcnt::Data)
    }
    #[doc = "Next transmit value is CRC value from TCRC"]
    #[inline(always)]
    pub fn crc(self) -> &'a mut crate::W<REG> {
        self.variant(Crcnt::Crc)
    }
}
#[doc = "CRC Calculation Enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Crcen {
    #[doc = "0: CRC calculation disabled"]
    Disabled = 0,
    #[doc = "1: CRC calculation enabled"]
    Enabled = 1,
}
impl From<Crcen> for bool {
    #[inline(always)]
    fn from(variant: Crcen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CRCEN` reader - CRC Calculation Enable"]
pub type CrcenR = crate::BitReader<Crcen>;
impl CrcenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Crcen {
        match self.bits {
            false => Crcen::Disabled,
            true => Crcen::Enabled,
        }
    }
    #[doc = "CRC calculation disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Crcen::Disabled
    }
    #[doc = "CRC calculation enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Crcen::Enabled
    }
}
#[doc = "Field `CRCEN` writer - CRC Calculation Enable"]
pub type CrcenW<'a, REG> = crate::BitWriter<'a, REG, Crcen>;
impl<'a, REG> CrcenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "CRC calculation disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Crcen::Disabled)
    }
    #[doc = "CRC calculation enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Crcen::Enabled)
    }
}
#[doc = "Bidirectional Transmit output enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bdoen {
    #[doc = "0: Receive-only mode"]
    ReceiveOnly = 0,
    #[doc = "1: Transmit-only mode"]
    TransmitOnly = 1,
}
impl From<Bdoen> for bool {
    #[inline(always)]
    fn from(variant: Bdoen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `BDOEN` reader - Bidirectional Transmit output enable"]
pub type BdoenR = crate::BitReader<Bdoen>;
impl BdoenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Bdoen {
        match self.bits {
            false => Bdoen::ReceiveOnly,
            true => Bdoen::TransmitOnly,
        }
    }
    #[doc = "Receive-only mode"]
    #[inline(always)]
    pub fn is_receive_only(&self) -> bool {
        *self == Bdoen::ReceiveOnly
    }
    #[doc = "Transmit-only mode"]
    #[inline(always)]
    pub fn is_transmit_only(&self) -> bool {
        *self == Bdoen::TransmitOnly
    }
}
#[doc = "Field `BDOEN` writer - Bidirectional Transmit output enable"]
pub type BdoenW<'a, REG> = crate::BitWriter<'a, REG, Bdoen>;
impl<'a, REG> BdoenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Receive-only mode"]
    #[inline(always)]
    pub fn receive_only(self) -> &'a mut crate::W<REG> {
        self.variant(Bdoen::ReceiveOnly)
    }
    #[doc = "Transmit-only mode"]
    #[inline(always)]
    pub fn transmit_only(self) -> &'a mut crate::W<REG> {
        self.variant(Bdoen::TransmitOnly)
    }
}
#[doc = "Bidirectional enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Bden {
    #[doc = "0: 2-line unidirectional data mode selected"]
    Unidirectional = 0,
    #[doc = "1: 1-line bidirectional data mode selected"]
    Bidirectional = 1,
}
impl From<Bden> for bool {
    #[inline(always)]
    fn from(variant: Bden) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `BDEN` reader - Bidirectional enable"]
pub type BdenR = crate::BitReader<Bden>;
impl BdenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Bden {
        match self.bits {
            false => Bden::Unidirectional,
            true => Bden::Bidirectional,
        }
    }
    #[doc = "2-line unidirectional data mode selected"]
    #[inline(always)]
    pub fn is_unidirectional(&self) -> bool {
        *self == Bden::Unidirectional
    }
    #[doc = "1-line bidirectional data mode selected"]
    #[inline(always)]
    pub fn is_bidirectional(&self) -> bool {
        *self == Bden::Bidirectional
    }
}
#[doc = "Field `BDEN` writer - Bidirectional enable"]
pub type BdenW<'a, REG> = crate::BitWriter<'a, REG, Bden>;
impl<'a, REG> BdenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "2-line unidirectional data mode selected"]
    #[inline(always)]
    pub fn unidirectional(self) -> &'a mut crate::W<REG> {
        self.variant(Bden::Unidirectional)
    }
    #[doc = "1-line bidirectional data mode selected"]
    #[inline(always)]
    pub fn bidirectional(self) -> &'a mut crate::W<REG> {
        self.variant(Bden::Bidirectional)
    }
}
impl R {
    #[doc = "Bit 0 - Clock Phase Selection"]
    #[inline(always)]
    pub fn ckph(&self) -> CkphR {
        CkphR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Clock polarity Selection"]
    #[inline(always)]
    pub fn ckpl(&self) -> CkplR {
        CkplR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Master Mode Enable"]
    #[inline(always)]
    pub fn mstmod(&self) -> MstmodR {
        MstmodR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bits 3:5 - Master Clock Prescaler Selection"]
    #[inline(always)]
    pub fn psc(&self) -> PscR {
        PscR::new(((self.bits >> 3) & 7) as u8)
    }
    #[doc = "Bit 6 - SPI enable"]
    #[inline(always)]
    pub fn spien(&self) -> SpienR {
        SpienR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - LSB First Mode"]
    #[inline(always)]
    pub fn lf(&self) -> LfR {
        LfR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - NSS Pin Selection In NSS Software Mode"]
    #[inline(always)]
    pub fn swnss(&self) -> SwnssR {
        SwnssR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - NSS Software Mode Selection"]
    #[inline(always)]
    pub fn swnssen(&self) -> SwnssenR {
        SwnssenR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Receive only"]
    #[inline(always)]
    pub fn ro(&self) -> RoR {
        RoR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Data frame format"]
    #[inline(always)]
    pub fn ff16(&self) -> Ff16R {
        Ff16R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - CRC Next Transfer"]
    #[inline(always)]
    pub fn crcnt(&self) -> CrcntR {
        CrcntR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - CRC Calculation Enable"]
    #[inline(always)]
    pub fn crcen(&self) -> CrcenR {
        CrcenR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Bidirectional Transmit output enable"]
    #[inline(always)]
    pub fn bdoen(&self) -> BdoenR {
        BdoenR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Bidirectional enable"]
    #[inline(always)]
    pub fn bden(&self) -> BdenR {
        BdenR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Clock Phase Selection"]
    #[inline(always)]
    #[must_use]
    pub fn ckph(&mut self) -> CkphW<Ctl0Spec> {
        CkphW::new(self, 0)
    }
    #[doc = "Bit 1 - Clock polarity Selection"]
    #[inline(always)]
    #[must_use]
    pub fn ckpl(&mut self) -> CkplW<Ctl0Spec> {
        CkplW::new(self, 1)
    }
    #[doc = "Bit 2 - Master Mode Enable"]
    #[inline(always)]
    #[must_use]
    pub fn mstmod(&mut self) -> MstmodW<Ctl0Spec> {
        MstmodW::new(self, 2)
    }
    #[doc = "Bits 3:5 - Master Clock Prescaler Selection"]
    #[inline(always)]
    #[must_use]
    pub fn psc(&mut self) -> PscW<Ctl0Spec> {
        PscW::new(self, 3)
    }
    #[doc = "Bit 6 - SPI enable"]
    #[inline(always)]
    #[must_use]
    pub fn spien(&mut self) -> SpienW<Ctl0Spec> {
        SpienW::new(self, 6)
    }
    #[doc = "Bit 7 - LSB First Mode"]
    #[inline(always)]
    #[must_use]
    pub fn lf(&mut self) -> LfW<Ctl0Spec> {
        LfW::new(self, 7)
    }
    #[doc = "Bit 8 - NSS Pin Selection In NSS Software Mode"]
    #[inline(always)]
    #[must_use]
    pub fn swnss(&mut self) -> SwnssW<Ctl0Spec> {
        SwnssW::new(self, 8)
    }
    #[doc = "Bit 9 - NSS Software Mode Selection"]
    #[inline(always)]
    #[must_use]
    pub fn swnssen(&mut self) -> SwnssenW<Ctl0Spec> {
        SwnssenW::new(self, 9)
    }
    #[doc = "Bit 10 - Receive only"]
    #[inline(always)]
    #[must_use]
    pub fn ro(&mut self) -> RoW<Ctl0Spec> {
        RoW::new(self, 10)
    }
    #[doc = "Bit 11 - Data frame format"]
    #[inline(always)]
    #[must_use]
    pub fn ff16(&mut self) -> Ff16W<Ctl0Spec> {
        Ff16W::new(self, 11)
    }
    #[doc = "Bit 12 - CRC Next Transfer"]
    #[inline(always)]
    #[must_use]
    pub fn crcnt(&mut self) -> CrcntW<Ctl0Spec> {
        CrcntW::new(self, 12)
    }
    #[doc = "Bit 13 - CRC Calculation Enable"]
    #[inline(always)]
    #[must_use]
    pub fn crcen(&mut self) -> CrcenW<Ctl0Spec> {
        CrcenW::new(self, 13)
    }
    #[doc = "Bit 14 - Bidirectional Transmit output enable"]
    #[inline(always)]
    #[must_use]
    pub fn bdoen(&mut self) -> BdoenW<Ctl0Spec> {
        BdoenW::new(self, 14)
    }
    #[doc = "Bit 15 - Bidirectional enable"]
    #[inline(always)]
    #[must_use]
    pub fn bden(&mut self) -> BdenW<Ctl0Spec> {
        BdenW::new(self, 15)
    }
}
#[doc = "control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl0Spec;
impl crate::RegisterSpec for Ctl0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl0::R`](R) reader structure"]
impl crate::Readable for Ctl0Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl0::W`](W) writer structure"]
impl crate::Writable for Ctl0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL0 to value 0"]
impl crate::Resettable for Ctl0Spec {
    const RESET_VALUE: u32 = 0;
}
