#[doc = "Register `STAT` reader"]
pub type R = crate::R<StatSpec>;
#[doc = "Register `STAT` writer"]
pub type W = crate::W<StatSpec>;
#[doc = "The flash is busy bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Busyr {
    #[doc = "0: No operation is in progress"]
    Inactive = 0,
    #[doc = "1: An operation is in progress"]
    Active = 1,
}
impl From<Busyr> for bool {
    #[inline(always)]
    fn from(variant: Busyr) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `BUSY` reader - The flash is busy bit"]
pub type BusyR = crate::BitReader<Busyr>;
impl BusyR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Busyr {
        match self.bits {
            false => Busyr::Inactive,
            true => Busyr::Active,
        }
    }
    #[doc = "No operation is in progress"]
    #[inline(always)]
    pub fn is_inactive(&self) -> bool {
        *self == Busyr::Inactive
    }
    #[doc = "An operation is in progress"]
    #[inline(always)]
    pub fn is_active(&self) -> bool {
        *self == Busyr::Active
    }
}
#[doc = "Program error flag bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pgerrr {
    #[doc = "0: There was no error"]
    NoError = 0,
    #[doc = "1: There was an error programming flash"]
    Error = 1,
}
impl From<Pgerrr> for bool {
    #[inline(always)]
    fn from(variant: Pgerrr) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `PGERR` reader - Program error flag bit"]
pub type PgerrR = crate::BitReader<Pgerrr>;
impl PgerrR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Pgerrr {
        match self.bits {
            false => Pgerrr::NoError,
            true => Pgerrr::Error,
        }
    }
    #[doc = "There was no error"]
    #[inline(always)]
    pub fn is_no_error(&self) -> bool {
        *self == Pgerrr::NoError
    }
    #[doc = "There was an error programming flash"]
    #[inline(always)]
    pub fn is_error(&self) -> bool {
        *self == Pgerrr::Error
    }
}
#[doc = "Program error flag bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PgerrwWO {
    #[doc = "1: Clears flag"]
    Clear = 1,
}
impl From<PgerrwWO> for bool {
    #[inline(always)]
    fn from(variant: PgerrwWO) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `PGERR` writer - Program error flag bit"]
pub type PgerrW<'a, REG> = crate::BitWriter<'a, REG, PgerrwWO>;
impl<'a, REG> PgerrW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Clears flag"]
    #[inline(always)]
    pub fn clear(self) -> &'a mut crate::W<REG> {
        self.variant(PgerrwWO::Clear)
    }
}
#[doc = "Field `PGAERR` reader - Program alignment error flag bit"]
pub type PgaerrR = crate::BitReader;
#[doc = "Field `PGAERR` writer - Program alignment error flag bit"]
pub type PgaerrW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Erase/Program protection error flag bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Wperrr {
    #[doc = "0: There was no error"]
    NoError = 0,
    #[doc = "1: There was an error erasing/programming protected pages"]
    Error = 1,
}
impl From<Wperrr> for bool {
    #[inline(always)]
    fn from(variant: Wperrr) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `WPERR` reader - Erase/Program protection error flag bit"]
pub type WperrR = crate::BitReader<Wperrr>;
impl WperrR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Wperrr {
        match self.bits {
            false => Wperrr::NoError,
            true => Wperrr::Error,
        }
    }
    #[doc = "There was no error"]
    #[inline(always)]
    pub fn is_no_error(&self) -> bool {
        *self == Wperrr::NoError
    }
    #[doc = "There was an error erasing/programming protected pages"]
    #[inline(always)]
    pub fn is_error(&self) -> bool {
        *self == Wperrr::Error
    }
}
#[doc = "Erase/Program protection error flag bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WperrwWO {
    #[doc = "1: Clears flag"]
    Clear = 1,
}
impl From<WperrwWO> for bool {
    #[inline(always)]
    fn from(variant: WperrwWO) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `WPERR` writer - Erase/Program protection error flag bit"]
pub type WperrW<'a, REG> = crate::BitWriter<'a, REG, WperrwWO>;
impl<'a, REG> WperrW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Clears flag"]
    #[inline(always)]
    pub fn clear(self) -> &'a mut crate::W<REG> {
        self.variant(WperrwWO::Clear)
    }
}
#[doc = "End of operation flag bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Endfr {
    #[doc = "0: No end of operation occurred"]
    NoEvent = 0,
    #[doc = "1: An end of operation event occurred"]
    Event = 1,
}
impl From<Endfr> for bool {
    #[inline(always)]
    fn from(variant: Endfr) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `ENDF` reader - End of operation flag bit"]
pub type EndfR = crate::BitReader<Endfr>;
impl EndfR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Endfr {
        match self.bits {
            false => Endfr::NoEvent,
            true => Endfr::Event,
        }
    }
    #[doc = "No end of operation occurred"]
    #[inline(always)]
    pub fn is_no_event(&self) -> bool {
        *self == Endfr::NoEvent
    }
    #[doc = "An end of operation event occurred"]
    #[inline(always)]
    pub fn is_event(&self) -> bool {
        *self == Endfr::Event
    }
}
#[doc = "End of operation flag bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EndfwWO {
    #[doc = "1: Clears flag"]
    Clear = 1,
}
impl From<EndfwWO> for bool {
    #[inline(always)]
    fn from(variant: EndfwWO) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `ENDF` writer - End of operation flag bit"]
pub type EndfW<'a, REG> = crate::BitWriter<'a, REG, EndfwWO>;
impl<'a, REG> EndfW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Clears flag"]
    #[inline(always)]
    pub fn clear(self) -> &'a mut crate::W<REG> {
        self.variant(EndfwWO::Clear)
    }
}
impl R {
    #[doc = "Bit 0 - The flash is busy bit"]
    #[inline(always)]
    pub fn busy(&self) -> BusyR {
        BusyR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 2 - Program error flag bit"]
    #[inline(always)]
    pub fn pgerr(&self) -> PgerrR {
        PgerrR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Program alignment error flag bit"]
    #[inline(always)]
    pub fn pgaerr(&self) -> PgaerrR {
        PgaerrR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Erase/Program protection error flag bit"]
    #[inline(always)]
    pub fn wperr(&self) -> WperrR {
        WperrR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - End of operation flag bit"]
    #[inline(always)]
    pub fn endf(&self) -> EndfR {
        EndfR::new(((self.bits >> 5) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 2 - Program error flag bit"]
    #[inline(always)]
    #[must_use]
    pub fn pgerr(&mut self) -> PgerrW<StatSpec> {
        PgerrW::new(self, 2)
    }
    #[doc = "Bit 3 - Program alignment error flag bit"]
    #[inline(always)]
    #[must_use]
    pub fn pgaerr(&mut self) -> PgaerrW<StatSpec> {
        PgaerrW::new(self, 3)
    }
    #[doc = "Bit 4 - Erase/Program protection error flag bit"]
    #[inline(always)]
    #[must_use]
    pub fn wperr(&mut self) -> WperrW<StatSpec> {
        WperrW::new(self, 4)
    }
    #[doc = "Bit 5 - End of operation flag bit"]
    #[inline(always)]
    #[must_use]
    pub fn endf(&mut self) -> EndfW<StatSpec> {
        EndfW::new(self, 5)
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
#[doc = "`reset()` method sets STAT to value 0"]
impl crate::Resettable for StatSpec {
    const RESET_VALUE: u32 = 0;
}
