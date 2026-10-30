#[doc = "Register `I2SCTL` reader"]
pub type R = crate::R<I2sctlSpec>;
#[doc = "Register `I2SCTL` writer"]
pub type W = crate::W<I2sctlSpec>;
#[doc = "Channel length (number of bits per audio channel)\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Chlen {
    #[doc = "0: 16-bit wide"]
    SixteenBit = 0,
    #[doc = "1: 32-bit wide"]
    ThirtyTwoBit = 1,
}
impl From<Chlen> for bool {
    #[inline(always)]
    fn from(variant: Chlen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CHLEN` reader - Channel length (number of bits per audio channel)"]
pub type ChlenR = crate::BitReader<Chlen>;
impl ChlenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Chlen {
        match self.bits {
            false => Chlen::SixteenBit,
            true => Chlen::ThirtyTwoBit,
        }
    }
    #[doc = "16-bit wide"]
    #[inline(always)]
    pub fn is_sixteen_bit(&self) -> bool {
        *self == Chlen::SixteenBit
    }
    #[doc = "32-bit wide"]
    #[inline(always)]
    pub fn is_thirty_two_bit(&self) -> bool {
        *self == Chlen::ThirtyTwoBit
    }
}
#[doc = "Field `CHLEN` writer - Channel length (number of bits per audio channel)"]
pub type ChlenW<'a, REG> = crate::BitWriter<'a, REG, Chlen>;
impl<'a, REG> ChlenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "16-bit wide"]
    #[inline(always)]
    pub fn sixteen_bit(self) -> &'a mut crate::W<REG> {
        self.variant(Chlen::SixteenBit)
    }
    #[doc = "32-bit wide"]
    #[inline(always)]
    pub fn thirty_two_bit(self) -> &'a mut crate::W<REG> {
        self.variant(Chlen::ThirtyTwoBit)
    }
}
#[doc = "Data length\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Dtlen {
    #[doc = "0: 16-bit data length"]
    SixteenBit = 0,
    #[doc = "1: 24-bit data length"]
    TwentyFourBit = 1,
    #[doc = "2: 32-bit data length"]
    ThirtyTwoBit = 2,
}
impl From<Dtlen> for u8 {
    #[inline(always)]
    fn from(variant: Dtlen) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for Dtlen {
    type Ux = u8;
}
#[doc = "Field `DTLEN` reader - Data length"]
pub type DtlenR = crate::FieldReader<Dtlen>;
impl DtlenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Option<Dtlen> {
        match self.bits {
            0 => Some(Dtlen::SixteenBit),
            1 => Some(Dtlen::TwentyFourBit),
            2 => Some(Dtlen::ThirtyTwoBit),
            _ => None,
        }
    }
    #[doc = "16-bit data length"]
    #[inline(always)]
    pub fn is_sixteen_bit(&self) -> bool {
        *self == Dtlen::SixteenBit
    }
    #[doc = "24-bit data length"]
    #[inline(always)]
    pub fn is_twenty_four_bit(&self) -> bool {
        *self == Dtlen::TwentyFourBit
    }
    #[doc = "32-bit data length"]
    #[inline(always)]
    pub fn is_thirty_two_bit(&self) -> bool {
        *self == Dtlen::ThirtyTwoBit
    }
}
#[doc = "Field `DTLEN` writer - Data length"]
pub type DtlenW<'a, REG> = crate::FieldWriter<'a, REG, 2, Dtlen>;
impl<'a, REG> DtlenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "16-bit data length"]
    #[inline(always)]
    pub fn sixteen_bit(self) -> &'a mut crate::W<REG> {
        self.variant(Dtlen::SixteenBit)
    }
    #[doc = "24-bit data length"]
    #[inline(always)]
    pub fn twenty_four_bit(self) -> &'a mut crate::W<REG> {
        self.variant(Dtlen::TwentyFourBit)
    }
    #[doc = "32-bit data length"]
    #[inline(always)]
    pub fn thirty_two_bit(self) -> &'a mut crate::W<REG> {
        self.variant(Dtlen::ThirtyTwoBit)
    }
}
#[doc = "Idle state clock polarity\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ckpl {
    #[doc = "0: I2S clock inactive state is low level"]
    IdleLow = 0,
    #[doc = "1: I2S clock inactive state is high level"]
    IdleHigh = 1,
}
impl From<Ckpl> for bool {
    #[inline(always)]
    fn from(variant: Ckpl) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CKPL` reader - Idle state clock polarity"]
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
    #[doc = "I2S clock inactive state is low level"]
    #[inline(always)]
    pub fn is_idle_low(&self) -> bool {
        *self == Ckpl::IdleLow
    }
    #[doc = "I2S clock inactive state is high level"]
    #[inline(always)]
    pub fn is_idle_high(&self) -> bool {
        *self == Ckpl::IdleHigh
    }
}
#[doc = "Field `CKPL` writer - Idle state clock polarity"]
pub type CkplW<'a, REG> = crate::BitWriter<'a, REG, Ckpl>;
impl<'a, REG> CkplW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "I2S clock inactive state is low level"]
    #[inline(always)]
    pub fn idle_low(self) -> &'a mut crate::W<REG> {
        self.variant(Ckpl::IdleLow)
    }
    #[doc = "I2S clock inactive state is high level"]
    #[inline(always)]
    pub fn idle_high(self) -> &'a mut crate::W<REG> {
        self.variant(Ckpl::IdleHigh)
    }
}
#[doc = "I2S standard selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum I2sstd {
    #[doc = "0: I2S Philips standard"]
    Philips = 0,
    #[doc = "1: MSB justified standard"]
    Msb = 1,
    #[doc = "2: LSB justified standard"]
    Lsb = 2,
    #[doc = "3: PCM standard"]
    Pcm = 3,
}
impl From<I2sstd> for u8 {
    #[inline(always)]
    fn from(variant: I2sstd) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for I2sstd {
    type Ux = u8;
}
#[doc = "Field `I2SSTD` reader - I2S standard selection"]
pub type I2sstdR = crate::FieldReader<I2sstd>;
impl I2sstdR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> I2sstd {
        match self.bits {
            0 => I2sstd::Philips,
            1 => I2sstd::Msb,
            2 => I2sstd::Lsb,
            3 => I2sstd::Pcm,
            _ => unreachable!(),
        }
    }
    #[doc = "I2S Philips standard"]
    #[inline(always)]
    pub fn is_philips(&self) -> bool {
        *self == I2sstd::Philips
    }
    #[doc = "MSB justified standard"]
    #[inline(always)]
    pub fn is_msb(&self) -> bool {
        *self == I2sstd::Msb
    }
    #[doc = "LSB justified standard"]
    #[inline(always)]
    pub fn is_lsb(&self) -> bool {
        *self == I2sstd::Lsb
    }
    #[doc = "PCM standard"]
    #[inline(always)]
    pub fn is_pcm(&self) -> bool {
        *self == I2sstd::Pcm
    }
}
#[doc = "Field `I2SSTD` writer - I2S standard selection"]
pub type I2sstdW<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, I2sstd>;
impl<'a, REG> I2sstdW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "I2S Philips standard"]
    #[inline(always)]
    pub fn philips(self) -> &'a mut crate::W<REG> {
        self.variant(I2sstd::Philips)
    }
    #[doc = "MSB justified standard"]
    #[inline(always)]
    pub fn msb(self) -> &'a mut crate::W<REG> {
        self.variant(I2sstd::Msb)
    }
    #[doc = "LSB justified standard"]
    #[inline(always)]
    pub fn lsb(self) -> &'a mut crate::W<REG> {
        self.variant(I2sstd::Lsb)
    }
    #[doc = "PCM standard"]
    #[inline(always)]
    pub fn pcm(self) -> &'a mut crate::W<REG> {
        self.variant(I2sstd::Pcm)
    }
}
#[doc = "PCM frame synchronization mode\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pcmsmod {
    #[doc = "0: Short frame synchronisation"]
    Short = 0,
    #[doc = "1: Long frame synchronisation"]
    Long = 1,
}
impl From<Pcmsmod> for bool {
    #[inline(always)]
    fn from(variant: Pcmsmod) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `PCMSMOD` reader - PCM frame synchronization mode"]
pub type PcmsmodR = crate::BitReader<Pcmsmod>;
impl PcmsmodR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Pcmsmod {
        match self.bits {
            false => Pcmsmod::Short,
            true => Pcmsmod::Long,
        }
    }
    #[doc = "Short frame synchronisation"]
    #[inline(always)]
    pub fn is_short(&self) -> bool {
        *self == Pcmsmod::Short
    }
    #[doc = "Long frame synchronisation"]
    #[inline(always)]
    pub fn is_long(&self) -> bool {
        *self == Pcmsmod::Long
    }
}
#[doc = "Field `PCMSMOD` writer - PCM frame synchronization mode"]
pub type PcmsmodW<'a, REG> = crate::BitWriter<'a, REG, Pcmsmod>;
impl<'a, REG> PcmsmodW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Short frame synchronisation"]
    #[inline(always)]
    pub fn short(self) -> &'a mut crate::W<REG> {
        self.variant(Pcmsmod::Short)
    }
    #[doc = "Long frame synchronisation"]
    #[inline(always)]
    pub fn long(self) -> &'a mut crate::W<REG> {
        self.variant(Pcmsmod::Long)
    }
}
#[doc = "I2S operation mode\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum I2sopmod {
    #[doc = "0: Slave - transmit"]
    SlaveTx = 0,
    #[doc = "1: Slave - receive"]
    SlaveRx = 1,
    #[doc = "2: Master - transmit"]
    MasterTx = 2,
    #[doc = "3: Master - receive"]
    MasterRx = 3,
}
impl From<I2sopmod> for u8 {
    #[inline(always)]
    fn from(variant: I2sopmod) -> Self {
        variant as _
    }
}
impl crate::FieldSpec for I2sopmod {
    type Ux = u8;
}
#[doc = "Field `I2SOPMOD` reader - I2S operation mode"]
pub type I2sopmodR = crate::FieldReader<I2sopmod>;
impl I2sopmodR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> I2sopmod {
        match self.bits {
            0 => I2sopmod::SlaveTx,
            1 => I2sopmod::SlaveRx,
            2 => I2sopmod::MasterTx,
            3 => I2sopmod::MasterRx,
            _ => unreachable!(),
        }
    }
    #[doc = "Slave - transmit"]
    #[inline(always)]
    pub fn is_slave_tx(&self) -> bool {
        *self == I2sopmod::SlaveTx
    }
    #[doc = "Slave - receive"]
    #[inline(always)]
    pub fn is_slave_rx(&self) -> bool {
        *self == I2sopmod::SlaveRx
    }
    #[doc = "Master - transmit"]
    #[inline(always)]
    pub fn is_master_tx(&self) -> bool {
        *self == I2sopmod::MasterTx
    }
    #[doc = "Master - receive"]
    #[inline(always)]
    pub fn is_master_rx(&self) -> bool {
        *self == I2sopmod::MasterRx
    }
}
#[doc = "Field `I2SOPMOD` writer - I2S operation mode"]
pub type I2sopmodW<'a, REG> = crate::FieldWriterSafe<'a, REG, 2, I2sopmod>;
impl<'a, REG> I2sopmodW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
    REG::Ux: From<u8>,
{
    #[doc = "Slave - transmit"]
    #[inline(always)]
    pub fn slave_tx(self) -> &'a mut crate::W<REG> {
        self.variant(I2sopmod::SlaveTx)
    }
    #[doc = "Slave - receive"]
    #[inline(always)]
    pub fn slave_rx(self) -> &'a mut crate::W<REG> {
        self.variant(I2sopmod::SlaveRx)
    }
    #[doc = "Master - transmit"]
    #[inline(always)]
    pub fn master_tx(self) -> &'a mut crate::W<REG> {
        self.variant(I2sopmod::MasterTx)
    }
    #[doc = "Master - receive"]
    #[inline(always)]
    pub fn master_rx(self) -> &'a mut crate::W<REG> {
        self.variant(I2sopmod::MasterRx)
    }
}
#[doc = "I2S Enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum I2sen {
    #[doc = "0: I2S peripheral is disabled"]
    Disabled = 0,
    #[doc = "1: I2S peripheral is enabled"]
    Enabled = 1,
}
impl From<I2sen> for bool {
    #[inline(always)]
    fn from(variant: I2sen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `I2SEN` reader - I2S Enable"]
pub type I2senR = crate::BitReader<I2sen>;
impl I2senR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> I2sen {
        match self.bits {
            false => I2sen::Disabled,
            true => I2sen::Enabled,
        }
    }
    #[doc = "I2S peripheral is disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == I2sen::Disabled
    }
    #[doc = "I2S peripheral is enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == I2sen::Enabled
    }
}
#[doc = "Field `I2SEN` writer - I2S Enable"]
pub type I2senW<'a, REG> = crate::BitWriter<'a, REG, I2sen>;
impl<'a, REG> I2senW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "I2S peripheral is disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(I2sen::Disabled)
    }
    #[doc = "I2S peripheral is enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(I2sen::Enabled)
    }
}
#[doc = "I2S mode selection\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum I2ssel {
    #[doc = "0: SPI mode is selected"]
    Spimode = 0,
    #[doc = "1: I2S mode is selected"]
    I2smode = 1,
}
impl From<I2ssel> for bool {
    #[inline(always)]
    fn from(variant: I2ssel) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `I2SSEL` reader - I2S mode selection"]
pub type I2sselR = crate::BitReader<I2ssel>;
impl I2sselR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> I2ssel {
        match self.bits {
            false => I2ssel::Spimode,
            true => I2ssel::I2smode,
        }
    }
    #[doc = "SPI mode is selected"]
    #[inline(always)]
    pub fn is_spimode(&self) -> bool {
        *self == I2ssel::Spimode
    }
    #[doc = "I2S mode is selected"]
    #[inline(always)]
    pub fn is_i2smode(&self) -> bool {
        *self == I2ssel::I2smode
    }
}
#[doc = "Field `I2SSEL` writer - I2S mode selection"]
pub type I2sselW<'a, REG> = crate::BitWriter<'a, REG, I2ssel>;
impl<'a, REG> I2sselW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "SPI mode is selected"]
    #[inline(always)]
    pub fn spimode(self) -> &'a mut crate::W<REG> {
        self.variant(I2ssel::Spimode)
    }
    #[doc = "I2S mode is selected"]
    #[inline(always)]
    pub fn i2smode(self) -> &'a mut crate::W<REG> {
        self.variant(I2ssel::I2smode)
    }
}
impl R {
    #[doc = "Bit 0 - Channel length (number of bits per audio channel)"]
    #[inline(always)]
    pub fn chlen(&self) -> ChlenR {
        ChlenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:2 - Data length"]
    #[inline(always)]
    pub fn dtlen(&self) -> DtlenR {
        DtlenR::new(((self.bits >> 1) & 3) as u8)
    }
    #[doc = "Bit 3 - Idle state clock polarity"]
    #[inline(always)]
    pub fn ckpl(&self) -> CkplR {
        CkplR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:5 - I2S standard selection"]
    #[inline(always)]
    pub fn i2sstd(&self) -> I2sstdR {
        I2sstdR::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bit 7 - PCM frame synchronization mode"]
    #[inline(always)]
    pub fn pcmsmod(&self) -> PcmsmodR {
        PcmsmodR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:9 - I2S operation mode"]
    #[inline(always)]
    pub fn i2sopmod(&self) -> I2sopmodR {
        I2sopmodR::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bit 10 - I2S Enable"]
    #[inline(always)]
    pub fn i2sen(&self) -> I2senR {
        I2senR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - I2S mode selection"]
    #[inline(always)]
    pub fn i2ssel(&self) -> I2sselR {
        I2sselR::new(((self.bits >> 11) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Channel length (number of bits per audio channel)"]
    #[inline(always)]
    #[must_use]
    pub fn chlen(&mut self) -> ChlenW<I2sctlSpec> {
        ChlenW::new(self, 0)
    }
    #[doc = "Bits 1:2 - Data length"]
    #[inline(always)]
    #[must_use]
    pub fn dtlen(&mut self) -> DtlenW<I2sctlSpec> {
        DtlenW::new(self, 1)
    }
    #[doc = "Bit 3 - Idle state clock polarity"]
    #[inline(always)]
    #[must_use]
    pub fn ckpl(&mut self) -> CkplW<I2sctlSpec> {
        CkplW::new(self, 3)
    }
    #[doc = "Bits 4:5 - I2S standard selection"]
    #[inline(always)]
    #[must_use]
    pub fn i2sstd(&mut self) -> I2sstdW<I2sctlSpec> {
        I2sstdW::new(self, 4)
    }
    #[doc = "Bit 7 - PCM frame synchronization mode"]
    #[inline(always)]
    #[must_use]
    pub fn pcmsmod(&mut self) -> PcmsmodW<I2sctlSpec> {
        PcmsmodW::new(self, 7)
    }
    #[doc = "Bits 8:9 - I2S operation mode"]
    #[inline(always)]
    #[must_use]
    pub fn i2sopmod(&mut self) -> I2sopmodW<I2sctlSpec> {
        I2sopmodW::new(self, 8)
    }
    #[doc = "Bit 10 - I2S Enable"]
    #[inline(always)]
    #[must_use]
    pub fn i2sen(&mut self) -> I2senW<I2sctlSpec> {
        I2senW::new(self, 10)
    }
    #[doc = "Bit 11 - I2S mode selection"]
    #[inline(always)]
    #[must_use]
    pub fn i2ssel(&mut self) -> I2sselW<I2sctlSpec> {
        I2sselW::new(self, 11)
    }
}
#[doc = "I2S control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`i2sctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`i2sctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct I2sctlSpec;
impl crate::RegisterSpec for I2sctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`i2sctl::R`](R) reader structure"]
impl crate::Readable for I2sctlSpec {}
#[doc = "`write(|w| ..)` method takes [`i2sctl::W`](W) writer structure"]
impl crate::Writable for I2sctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets I2SCTL to value 0"]
impl crate::Resettable for I2sctlSpec {
    const RESET_VALUE: u32 = 0;
}
