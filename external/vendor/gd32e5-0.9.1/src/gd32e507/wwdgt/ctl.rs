#[doc = "Register `CTL` reader"]
pub type R = crate::R<CtlSpec>;
#[doc = "Register `CTL` writer"]
pub type W = crate::W<CtlSpec>;
#[doc = "Field `CNT` reader - 7-bit counter"]
pub type CntR = crate::FieldReader;
#[doc = "Field `CNT` writer - 7-bit counter"]
pub type CntW<'a, REG> = crate::FieldWriterSafe<'a, REG, 7>;
#[doc = "Activation bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Wdgten {
    #[doc = "0: Watchdog disabled"]
    Disabled = 0,
    #[doc = "1: Watchdog enabled"]
    Enabled = 1,
}
impl From<Wdgten> for bool {
    #[inline(always)]
    fn from(variant: Wdgten) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `WDGTEN` reader - Activation bit"]
pub type WdgtenR = crate::BitReader<Wdgten>;
impl WdgtenR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Wdgten {
        match self.bits {
            false => Wdgten::Disabled,
            true => Wdgten::Enabled,
        }
    }
    #[doc = "Watchdog disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Wdgten::Disabled
    }
    #[doc = "Watchdog enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Wdgten::Enabled
    }
}
#[doc = "Field `WDGTEN` writer - Activation bit"]
pub type WdgtenW<'a, REG> = crate::BitWriter<'a, REG, Wdgten>;
impl<'a, REG> WdgtenW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Watchdog disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Wdgten::Disabled)
    }
    #[doc = "Watchdog enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Wdgten::Enabled)
    }
}
impl R {
    #[doc = "Bits 0:6 - 7-bit counter"]
    #[inline(always)]
    pub fn cnt(&self) -> CntR {
        CntR::new((self.bits & 0x7f) as u8)
    }
    #[doc = "Bit 7 - Activation bit"]
    #[inline(always)]
    pub fn wdgten(&self) -> WdgtenR {
        WdgtenR::new(((self.bits >> 7) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:6 - 7-bit counter"]
    #[inline(always)]
    #[must_use]
    pub fn cnt(&mut self) -> CntW<CtlSpec> {
        CntW::new(self, 0)
    }
    #[doc = "Bit 7 - Activation bit"]
    #[inline(always)]
    #[must_use]
    pub fn wdgten(&mut self) -> WdgtenW<CtlSpec> {
        WdgtenW::new(self, 7)
    }
}
#[doc = "Control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CtlSpec;
impl crate::RegisterSpec for CtlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl::R`](R) reader structure"]
impl crate::Readable for CtlSpec {}
#[doc = "`write(|w| ..)` method takes [`ctl::W`](W) writer structure"]
impl crate::Writable for CtlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL to value 0x7f"]
impl crate::Resettable for CtlSpec {
    const RESET_VALUE: u32 = 0x7f;
}
