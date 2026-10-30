#[doc = "Register `INTC` writer"]
pub type W = crate::W<IntcSpec>;
#[doc = "Clear global interrupt flag of channel 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Gifc0 {
    #[doc = "1: Clears the GIF flag in INTF"]
    Clear = 1,
}
impl From<Gifc0> for bool {
    #[inline(always)]
    fn from(variant: Gifc0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `GIFC0` writer - Clear global interrupt flag of channel 0"]
pub type Gifc0W<'a, REG> = crate::BitWriter<'a, REG, Gifc0>;
impl<'a, REG> Gifc0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Clears the GIF flag in INTF"]
    #[inline(always)]
    pub fn clear(self) -> &'a mut crate::W<REG> {
        self.variant(Gifc0::Clear)
    }
}
#[doc = "Clear bit for full transfer finish flag of channel 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ftfifc0 {
    #[doc = "1: Clears the FDFIF flag in INTF"]
    Clear = 1,
}
impl From<Ftfifc0> for bool {
    #[inline(always)]
    fn from(variant: Ftfifc0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `FTFIFC0` writer - Clear bit for full transfer finish flag of channel 0"]
pub type Ftfifc0W<'a, REG> = crate::BitWriter<'a, REG, Ftfifc0>;
impl<'a, REG> Ftfifc0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Clears the FDFIF flag in INTF"]
    #[inline(always)]
    pub fn clear(self) -> &'a mut crate::W<REG> {
        self.variant(Ftfifc0::Clear)
    }
}
#[doc = "Clear bit for half transfer finish flag of channel 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Htfifc0 {
    #[doc = "1: Clears the HTFIF flag in INTF"]
    Clear = 1,
}
impl From<Htfifc0> for bool {
    #[inline(always)]
    fn from(variant: Htfifc0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `HTFIFC0` writer - Clear bit for half transfer finish flag of channel 0"]
pub type Htfifc0W<'a, REG> = crate::BitWriter<'a, REG, Htfifc0>;
impl<'a, REG> Htfifc0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Clears the HTFIF flag in INTF"]
    #[inline(always)]
    pub fn clear(self) -> &'a mut crate::W<REG> {
        self.variant(Htfifc0::Clear)
    }
}
#[doc = "Clear bit for error flag of channel 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Errifc0 {
    #[doc = "1: Clears the ERRIF flag in INTF"]
    Clear = 1,
}
impl From<Errifc0> for bool {
    #[inline(always)]
    fn from(variant: Errifc0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `ERRIFC0` writer - Clear bit for error flag of channel 0"]
pub type Errifc0W<'a, REG> = crate::BitWriter<'a, REG, Errifc0>;
impl<'a, REG> Errifc0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Clears the ERRIF flag in INTF"]
    #[inline(always)]
    pub fn clear(self) -> &'a mut crate::W<REG> {
        self.variant(Errifc0::Clear)
    }
}
#[doc = "Field `ERRIFC1` writer - Clear bit for error flag of channel 1"]
pub use Errifc0W as Errifc1W;
#[doc = "Field `ERRIFC2` writer - Clear bit for error flag of channel 2"]
pub use Errifc0W as Errifc2W;
#[doc = "Field `ERRIFC3` writer - Clear bit for error flag of channel 3"]
pub use Errifc0W as Errifc3W;
#[doc = "Field `ERRIFC4` writer - Clear bit for error flag of channel 4"]
pub use Errifc0W as Errifc4W;
#[doc = "Field `FTFIFC1` writer - Clear bit for full transfer finish flag of channel 1"]
pub use Ftfifc0W as Ftfifc1W;
#[doc = "Field `FTFIFC2` writer - Clear bit for full transfer finish flag of channel 2"]
pub use Ftfifc0W as Ftfifc2W;
#[doc = "Field `FTFIFC3` writer - Clear bit for full transfer finish flag of channel 3"]
pub use Ftfifc0W as Ftfifc3W;
#[doc = "Field `FTFIFC4` writer - Clear bit for full transfer finish flag of channel 4"]
pub use Ftfifc0W as Ftfifc4W;
#[doc = "Field `GIFC1` writer - Clear global interrupt flag of channel 1"]
pub use Gifc0W as Gifc1W;
#[doc = "Field `GIFC2` writer - Clear global interrupt flag of channel 2"]
pub use Gifc0W as Gifc2W;
#[doc = "Field `GIFC3` writer - Clear global interrupt flag of channel 3"]
pub use Gifc0W as Gifc3W;
#[doc = "Field `GIFC4` writer - Clear global interrupt flag of channel 4"]
pub use Gifc0W as Gifc4W;
#[doc = "Field `HTFIFC1` writer - Clear bit for half transfer finish flag of channel 1"]
pub use Htfifc0W as Htfifc1W;
#[doc = "Field `HTFIFC2` writer - Clear bit for half transfer finish flag of channel 2"]
pub use Htfifc0W as Htfifc2W;
#[doc = "Field `HTFIFC3` writer - Clear bit for half transfer finish flag of channel 3"]
pub use Htfifc0W as Htfifc3W;
#[doc = "Field `HTFIFC4` writer - Clear bit for half transfer finish flag of channel 4"]
pub use Htfifc0W as Htfifc4W;
impl W {
    #[doc = "Bit 0 - Clear global interrupt flag of channel 0"]
    #[inline(always)]
    #[must_use]
    pub fn gifc0(&mut self) -> Gifc0W<IntcSpec> {
        Gifc0W::new(self, 0)
    }
    #[doc = "Bit 1 - Clear bit for full transfer finish flag of channel 0"]
    #[inline(always)]
    #[must_use]
    pub fn ftfifc0(&mut self) -> Ftfifc0W<IntcSpec> {
        Ftfifc0W::new(self, 1)
    }
    #[doc = "Bit 2 - Clear bit for half transfer finish flag of channel 0"]
    #[inline(always)]
    #[must_use]
    pub fn htfifc0(&mut self) -> Htfifc0W<IntcSpec> {
        Htfifc0W::new(self, 2)
    }
    #[doc = "Bit 3 - Clear bit for error flag of channel 0"]
    #[inline(always)]
    #[must_use]
    pub fn errifc0(&mut self) -> Errifc0W<IntcSpec> {
        Errifc0W::new(self, 3)
    }
    #[doc = "Bit 4 - Clear global interrupt flag of channel 1"]
    #[inline(always)]
    #[must_use]
    pub fn gifc1(&mut self) -> Gifc1W<IntcSpec> {
        Gifc1W::new(self, 4)
    }
    #[doc = "Bit 5 - Clear bit for full transfer finish flag of channel 1"]
    #[inline(always)]
    #[must_use]
    pub fn ftfifc1(&mut self) -> Ftfifc1W<IntcSpec> {
        Ftfifc1W::new(self, 5)
    }
    #[doc = "Bit 6 - Clear bit for half transfer finish flag of channel 1"]
    #[inline(always)]
    #[must_use]
    pub fn htfifc1(&mut self) -> Htfifc1W<IntcSpec> {
        Htfifc1W::new(self, 6)
    }
    #[doc = "Bit 7 - Clear bit for error flag of channel 1"]
    #[inline(always)]
    #[must_use]
    pub fn errifc1(&mut self) -> Errifc1W<IntcSpec> {
        Errifc1W::new(self, 7)
    }
    #[doc = "Bit 8 - Clear global interrupt flag of channel 2"]
    #[inline(always)]
    #[must_use]
    pub fn gifc2(&mut self) -> Gifc2W<IntcSpec> {
        Gifc2W::new(self, 8)
    }
    #[doc = "Bit 9 - Clear bit for full transfer finish flag of channel 2"]
    #[inline(always)]
    #[must_use]
    pub fn ftfifc2(&mut self) -> Ftfifc2W<IntcSpec> {
        Ftfifc2W::new(self, 9)
    }
    #[doc = "Bit 10 - Clear bit for half transfer finish flag of channel 2"]
    #[inline(always)]
    #[must_use]
    pub fn htfifc2(&mut self) -> Htfifc2W<IntcSpec> {
        Htfifc2W::new(self, 10)
    }
    #[doc = "Bit 11 - Clear bit for error flag of channel 2"]
    #[inline(always)]
    #[must_use]
    pub fn errifc2(&mut self) -> Errifc2W<IntcSpec> {
        Errifc2W::new(self, 11)
    }
    #[doc = "Bit 12 - Clear global interrupt flag of channel 3"]
    #[inline(always)]
    #[must_use]
    pub fn gifc3(&mut self) -> Gifc3W<IntcSpec> {
        Gifc3W::new(self, 12)
    }
    #[doc = "Bit 13 - Clear bit for full transfer finish flag of channel 3"]
    #[inline(always)]
    #[must_use]
    pub fn ftfifc3(&mut self) -> Ftfifc3W<IntcSpec> {
        Ftfifc3W::new(self, 13)
    }
    #[doc = "Bit 14 - Clear bit for half transfer finish flag of channel 3"]
    #[inline(always)]
    #[must_use]
    pub fn htfifc3(&mut self) -> Htfifc3W<IntcSpec> {
        Htfifc3W::new(self, 14)
    }
    #[doc = "Bit 15 - Clear bit for error flag of channel 3"]
    #[inline(always)]
    #[must_use]
    pub fn errifc3(&mut self) -> Errifc3W<IntcSpec> {
        Errifc3W::new(self, 15)
    }
    #[doc = "Bit 16 - Clear global interrupt flag of channel 4"]
    #[inline(always)]
    #[must_use]
    pub fn gifc4(&mut self) -> Gifc4W<IntcSpec> {
        Gifc4W::new(self, 16)
    }
    #[doc = "Bit 17 - Clear bit for full transfer finish flag of channel 4"]
    #[inline(always)]
    #[must_use]
    pub fn ftfifc4(&mut self) -> Ftfifc4W<IntcSpec> {
        Ftfifc4W::new(self, 17)
    }
    #[doc = "Bit 18 - Clear bit for half transfer finish flag of channel 4"]
    #[inline(always)]
    #[must_use]
    pub fn htfifc4(&mut self) -> Htfifc4W<IntcSpec> {
        Htfifc4W::new(self, 18)
    }
    #[doc = "Bit 19 - Clear bit for error flag of channel 4"]
    #[inline(always)]
    #[must_use]
    pub fn errifc4(&mut self) -> Errifc4W<IntcSpec> {
        Errifc4W::new(self, 19)
    }
}
#[doc = "Interrupt flag clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`intc::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IntcSpec;
impl crate::RegisterSpec for IntcSpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`intc::W`](W) writer structure"]
impl crate::Writable for IntcSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets INTC to value 0"]
impl crate::Resettable for IntcSpec {
    const RESET_VALUE: u32 = 0;
}
