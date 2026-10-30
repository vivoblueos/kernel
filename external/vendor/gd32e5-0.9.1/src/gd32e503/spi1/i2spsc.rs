#[doc = "Register `I2SPSC` reader"]
pub type R = crate::R<I2spscSpec>;
#[doc = "Register `I2SPSC` writer"]
pub type W = crate::W<I2spscSpec>;
#[doc = "Field `DIV` reader - Dividing factor for the prescaler"]
pub type DivR = crate::FieldReader;
#[doc = "Field `DIV` writer - Dividing factor for the prescaler"]
pub type DivW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Odd factor for the prescaler\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Of {
    #[doc = "0: Real divider value is DIV * 2"]
    Even = 0,
    #[doc = "1: Real divider value is (DIV * 2) + 1"]
    Odd = 1,
}
impl From<Of> for bool {
    #[inline(always)]
    fn from(variant: Of) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `OF` reader - Odd factor for the prescaler"]
pub type OfR = crate::BitReader<Of>;
impl OfR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Of {
        match self.bits {
            false => Of::Even,
            true => Of::Odd,
        }
    }
    #[doc = "Real divider value is DIV * 2"]
    #[inline(always)]
    pub fn is_even(&self) -> bool {
        *self == Of::Even
    }
    #[doc = "Real divider value is (DIV * 2) + 1"]
    #[inline(always)]
    pub fn is_odd(&self) -> bool {
        *self == Of::Odd
    }
}
#[doc = "Field `OF` writer - Odd factor for the prescaler"]
pub type OfW<'a, REG> = crate::BitWriter<'a, REG, Of>;
impl<'a, REG> OfW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Real divider value is DIV * 2"]
    #[inline(always)]
    pub fn even(self) -> &'a mut crate::W<REG> {
        self.variant(Of::Even)
    }
    #[doc = "Real divider value is (DIV * 2) + 1"]
    #[inline(always)]
    pub fn odd(self) -> &'a mut crate::W<REG> {
        self.variant(Of::Odd)
    }
}
#[doc = "I2S_MCK output enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mckoen {
    #[doc = "0: Master clock output is disabled"]
    Disabled = 0,
    #[doc = "1: Master clock output is enabled"]
    Enabled = 1,
}
impl From<Mckoen> for bool {
    #[inline(always)]
    fn from(variant: Mckoen) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `MCKOEN` reader - I2S_MCK output enable"]
pub type MckoenR = crate::BitReader<Mckoen>;
impl MckoenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Mckoen {
        match self.bits {
            false => Mckoen::Disabled,
            true => Mckoen::Enabled,
        }
    }
    #[doc = "Master clock output is disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Mckoen::Disabled
    }
    #[doc = "Master clock output is enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Mckoen::Enabled
    }
}
#[doc = "Field `MCKOEN` writer - I2S_MCK output enable"]
pub type MckoenW<'a, REG> = crate::BitWriter<'a, REG, Mckoen>;
impl<'a, REG> MckoenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Master clock output is disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Mckoen::Disabled)
    }
    #[doc = "Master clock output is enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Mckoen::Enabled)
    }
}
impl R {
    #[doc = "Bits 0:7 - Dividing factor for the prescaler"]
    #[inline(always)]
    pub fn div(&self) -> DivR {
        DivR::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bit 8 - Odd factor for the prescaler"]
    #[inline(always)]
    pub fn of(&self) -> OfR {
        OfR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - I2S_MCK output enable"]
    #[inline(always)]
    pub fn mckoen(&self) -> MckoenR {
        MckoenR::new(((self.bits >> 9) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:7 - Dividing factor for the prescaler"]
    #[inline(always)]
    #[must_use]
    pub fn div(&mut self) -> DivW<I2spscSpec> {
        DivW::new(self, 0)
    }
    #[doc = "Bit 8 - Odd factor for the prescaler"]
    #[inline(always)]
    #[must_use]
    pub fn of(&mut self) -> OfW<I2spscSpec> {
        OfW::new(self, 8)
    }
    #[doc = "Bit 9 - I2S_MCK output enable"]
    #[inline(always)]
    #[must_use]
    pub fn mckoen(&mut self) -> MckoenW<I2spscSpec> {
        MckoenW::new(self, 9)
    }
}
#[doc = "I2S prescaler register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`i2spsc::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`i2spsc::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct I2spscSpec;
impl crate::RegisterSpec for I2spscSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`i2spsc::R`](R) reader structure"]
impl crate::Readable for I2spscSpec {}
#[doc = "`write(|w| ..)` method takes [`i2spsc::W`](W) writer structure"]
impl crate::Writable for I2spscSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets I2SPSC to value 0x02"]
impl crate::Resettable for I2spscSpec {
    const RESET_VALUE: u32 = 0x02;
}
