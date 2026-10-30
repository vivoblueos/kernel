#[doc = "Register `CTL1` reader"]
pub type R = crate::R<Ctl1Spec>;
#[doc = "Register `CTL1` writer"]
pub type W = crate::W<Ctl1Spec>;
#[doc = "Rx buffer DMA enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dmaren {
    #[doc = "0: Rx buffer DMA disabled"]
    Disabled = 0,
    #[doc = "1: Rx buffer DMA enabled"]
    Enabled = 1,
}
impl From<Dmaren> for bool {
    #[inline(always)]
    fn from(variant: Dmaren) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `DMAREN` reader - Rx buffer DMA enable"]
pub type DmarenR = crate::BitReader<Dmaren>;
impl DmarenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Dmaren {
        match self.bits {
            false => Dmaren::Disabled,
            true => Dmaren::Enabled,
        }
    }
    #[doc = "Rx buffer DMA disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Dmaren::Disabled
    }
    #[doc = "Rx buffer DMA enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Dmaren::Enabled
    }
}
#[doc = "Field `DMAREN` writer - Rx buffer DMA enable"]
pub type DmarenW<'a, REG> = crate::BitWriter<'a, REG, Dmaren>;
impl<'a, REG> DmarenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Rx buffer DMA disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Dmaren::Disabled)
    }
    #[doc = "Rx buffer DMA enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Dmaren::Enabled)
    }
}
#[doc = "Transmit Buffer DMA Enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dmaten {
    #[doc = "0: Tx buffer DMA disabled"]
    Disabled = 0,
    #[doc = "1: Tx buffer DMA enabled"]
    Enabled = 1,
}
impl From<Dmaten> for bool {
    #[inline(always)]
    fn from(variant: Dmaten) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `DMATEN` reader - Transmit Buffer DMA Enable"]
pub type DmatenR = crate::BitReader<Dmaten>;
impl DmatenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Dmaten {
        match self.bits {
            false => Dmaten::Disabled,
            true => Dmaten::Enabled,
        }
    }
    #[doc = "Tx buffer DMA disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Dmaten::Disabled
    }
    #[doc = "Tx buffer DMA enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Dmaten::Enabled
    }
}
#[doc = "Field `DMATEN` writer - Transmit Buffer DMA Enable"]
pub type DmatenW<'a, REG> = crate::BitWriter<'a, REG, Dmaten>;
impl<'a, REG> DmatenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Tx buffer DMA disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Dmaten::Disabled)
    }
    #[doc = "Tx buffer DMA enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Dmaten::Enabled)
    }
}
#[doc = "Drive NSS Output\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Nssdrv {
    #[doc = "0: NSS output is disabled in master mode"]
    Disabled = 0,
    #[doc = "1: NSS output is enabled in master mode"]
    Enabled = 1,
}
impl From<Nssdrv> for bool {
    #[inline(always)]
    fn from(variant: Nssdrv) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `NSSDRV` reader - Drive NSS Output"]
pub type NssdrvR = crate::BitReader<Nssdrv>;
impl NssdrvR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Nssdrv {
        match self.bits {
            false => Nssdrv::Disabled,
            true => Nssdrv::Enabled,
        }
    }
    #[doc = "NSS output is disabled in master mode"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Nssdrv::Disabled
    }
    #[doc = "NSS output is enabled in master mode"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Nssdrv::Enabled
    }
}
#[doc = "Field `NSSDRV` writer - Drive NSS Output"]
pub type NssdrvW<'a, REG> = crate::BitWriter<'a, REG, Nssdrv>;
impl<'a, REG> NssdrvW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "NSS output is disabled in master mode"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Nssdrv::Disabled)
    }
    #[doc = "NSS output is enabled in master mode"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Nssdrv::Enabled)
    }
}
#[doc = "Field `NSSP` reader - SPI NSS pulse mode Enable"]
pub type NsspR = crate::BitReader;
#[doc = "Field `NSSP` writer - SPI NSS pulse mode Enable"]
pub type NsspW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TMOD` reader - SPI TI Mode Enable"]
pub type TmodR = crate::BitReader;
#[doc = "Field `TMOD` writer - SPI TI Mode Enable"]
pub type TmodW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Error interrupt enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Errie {
    #[doc = "0: Error interrupt disabled"]
    Disabled = 0,
    #[doc = "1: Error interrupt enabled"]
    Enabled = 1,
}
impl From<Errie> for bool {
    #[inline(always)]
    fn from(variant: Errie) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `ERRIE` reader - Error interrupt enable"]
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
    #[doc = "Error interrupt disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Errie::Disabled
    }
    #[doc = "Error interrupt enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Errie::Enabled
    }
}
#[doc = "Field `ERRIE` writer - Error interrupt enable"]
pub type ErrieW<'a, REG> = crate::BitWriter<'a, REG, Errie>;
impl<'a, REG> ErrieW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Error interrupt disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Errie::Disabled)
    }
    #[doc = "Error interrupt enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Errie::Enabled)
    }
}
#[doc = "RX buffer not empty interrupt enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rbneie {
    #[doc = "0: RBNE interrupt disabled"]
    Disabled = 0,
    #[doc = "1: RBNE interrupt enabled"]
    Enabled = 1,
}
impl From<Rbneie> for bool {
    #[inline(always)]
    fn from(variant: Rbneie) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `RBNEIE` reader - RX buffer not empty interrupt enable"]
pub type RbneieR = crate::BitReader<Rbneie>;
impl RbneieR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Rbneie {
        match self.bits {
            false => Rbneie::Disabled,
            true => Rbneie::Enabled,
        }
    }
    #[doc = "RBNE interrupt disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Rbneie::Disabled
    }
    #[doc = "RBNE interrupt enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Rbneie::Enabled
    }
}
#[doc = "Field `RBNEIE` writer - RX buffer not empty interrupt enable"]
pub type RbneieW<'a, REG> = crate::BitWriter<'a, REG, Rbneie>;
impl<'a, REG> RbneieW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "RBNE interrupt disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Rbneie::Disabled)
    }
    #[doc = "RBNE interrupt enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Rbneie::Enabled)
    }
}
#[doc = "Tx buffer empty interrupt enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tbeie {
    #[doc = "0: TBE interrupt disabled"]
    Disabled = 0,
    #[doc = "1: TBE interrupt enabled"]
    Enabled = 1,
}
impl From<Tbeie> for bool {
    #[inline(always)]
    fn from(variant: Tbeie) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `TBEIE` reader - Tx buffer empty interrupt enable"]
pub type TbeieR = crate::BitReader<Tbeie>;
impl TbeieR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Tbeie {
        match self.bits {
            false => Tbeie::Disabled,
            true => Tbeie::Enabled,
        }
    }
    #[doc = "TBE interrupt disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Tbeie::Disabled
    }
    #[doc = "TBE interrupt enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Tbeie::Enabled
    }
}
#[doc = "Field `TBEIE` writer - Tx buffer empty interrupt enable"]
pub type TbeieW<'a, REG> = crate::BitWriter<'a, REG, Tbeie>;
impl<'a, REG> TbeieW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "TBE interrupt disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Tbeie::Disabled)
    }
    #[doc = "TBE interrupt enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Tbeie::Enabled)
    }
}
impl R {
    #[doc = "Bit 0 - Rx buffer DMA enable"]
    #[inline(always)]
    pub fn dmaren(&self) -> DmarenR {
        DmarenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Transmit Buffer DMA Enable"]
    #[inline(always)]
    pub fn dmaten(&self) -> DmatenR {
        DmatenR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Drive NSS Output"]
    #[inline(always)]
    pub fn nssdrv(&self) -> NssdrvR {
        NssdrvR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - SPI NSS pulse mode Enable"]
    #[inline(always)]
    pub fn nssp(&self) -> NsspR {
        NsspR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - SPI TI Mode Enable"]
    #[inline(always)]
    pub fn tmod(&self) -> TmodR {
        TmodR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Error interrupt enable"]
    #[inline(always)]
    pub fn errie(&self) -> ErrieR {
        ErrieR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - RX buffer not empty interrupt enable"]
    #[inline(always)]
    pub fn rbneie(&self) -> RbneieR {
        RbneieR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Tx buffer empty interrupt enable"]
    #[inline(always)]
    pub fn tbeie(&self) -> TbeieR {
        TbeieR::new(((self.bits >> 7) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Rx buffer DMA enable"]
    #[inline(always)]
    #[must_use]
    pub fn dmaren(&mut self) -> DmarenW<Ctl1Spec> {
        DmarenW::new(self, 0)
    }
    #[doc = "Bit 1 - Transmit Buffer DMA Enable"]
    #[inline(always)]
    #[must_use]
    pub fn dmaten(&mut self) -> DmatenW<Ctl1Spec> {
        DmatenW::new(self, 1)
    }
    #[doc = "Bit 2 - Drive NSS Output"]
    #[inline(always)]
    #[must_use]
    pub fn nssdrv(&mut self) -> NssdrvW<Ctl1Spec> {
        NssdrvW::new(self, 2)
    }
    #[doc = "Bit 3 - SPI NSS pulse mode Enable"]
    #[inline(always)]
    #[must_use]
    pub fn nssp(&mut self) -> NsspW<Ctl1Spec> {
        NsspW::new(self, 3)
    }
    #[doc = "Bit 4 - SPI TI Mode Enable"]
    #[inline(always)]
    #[must_use]
    pub fn tmod(&mut self) -> TmodW<Ctl1Spec> {
        TmodW::new(self, 4)
    }
    #[doc = "Bit 5 - Error interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn errie(&mut self) -> ErrieW<Ctl1Spec> {
        ErrieW::new(self, 5)
    }
    #[doc = "Bit 6 - RX buffer not empty interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rbneie(&mut self) -> RbneieW<Ctl1Spec> {
        RbneieW::new(self, 6)
    }
    #[doc = "Bit 7 - Tx buffer empty interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn tbeie(&mut self) -> TbeieW<Ctl1Spec> {
        TbeieW::new(self, 7)
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
