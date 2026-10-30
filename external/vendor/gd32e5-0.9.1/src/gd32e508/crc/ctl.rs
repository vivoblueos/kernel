#[doc = "Register `CTL` reader"]
pub type R = crate::R<CtlSpec>;
#[doc = "Register `CTL` writer"]
pub type W = crate::W<CtlSpec>;
#[doc = "reset bit\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rstw {
    #[doc = "1: Resets the DATA register to IDATA, with no effect on FDATA"]
    Reset = 1,
}
impl From<Rstw> for bool {
    #[inline(always)]
    fn from(variant: Rstw) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `RST` reader - reset bit"]
pub type RstR = crate::BitReader<Rstw>;
impl RstR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Option<Rstw> {
        match self.bits {
            true => Some(Rstw::Reset),
            _ => None,
        }
    }
    #[doc = "Resets the DATA register to IDATA, with no effect on FDATA"]
    #[inline(always)]
    pub fn is_reset(&self) -> bool {
        *self == Rstw::Reset
    }
}
#[doc = "Field `RST` writer - reset bit"]
pub type RstW<'a, REG> = crate::BitWriter<'a, REG, Rstw>;
impl<'a, REG> RstW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Resets the DATA register to IDATA, with no effect on FDATA"]
    #[inline(always)]
    pub fn reset(self) -> &'a mut crate::W<REG> {
        self.variant(Rstw::Reset)
    }
}
#[doc = "Field `PS` reader - Size of polynomial"]
pub type PsR = crate::FieldReader;
#[doc = "Field `PS` writer - Size of polynomial"]
pub type PsW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `REV_I` reader - Reverse type for input data"]
pub type RevIR = crate::FieldReader;
#[doc = "Field `REV_I` writer - Reverse type for input data"]
pub type RevIW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `REV_O` reader - Reverse output data value in bit order"]
pub type RevOR = crate::BitReader;
#[doc = "Field `REV_O` writer - Reverse output data value in bit order"]
pub type RevOW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - reset bit"]
    #[inline(always)]
    pub fn rst(&self) -> RstR {
        RstR::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 3:4 - Size of polynomial"]
    #[inline(always)]
    pub fn ps(&self) -> PsR {
        PsR::new(((self.bits >> 3) & 3) as u8)
    }
    #[doc = "Bits 5:6 - Reverse type for input data"]
    #[inline(always)]
    pub fn rev_i(&self) -> RevIR {
        RevIR::new(((self.bits >> 5) & 3) as u8)
    }
    #[doc = "Bit 7 - Reverse output data value in bit order"]
    #[inline(always)]
    pub fn rev_o(&self) -> RevOR {
        RevOR::new(((self.bits >> 7) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - reset bit"]
    #[inline(always)]
    #[must_use]
    pub fn rst(&mut self) -> RstW<CtlSpec> {
        RstW::new(self, 0)
    }
    #[doc = "Bits 3:4 - Size of polynomial"]
    #[inline(always)]
    #[must_use]
    pub fn ps(&mut self) -> PsW<CtlSpec> {
        PsW::new(self, 3)
    }
    #[doc = "Bits 5:6 - Reverse type for input data"]
    #[inline(always)]
    #[must_use]
    pub fn rev_i(&mut self) -> RevIW<CtlSpec> {
        RevIW::new(self, 5)
    }
    #[doc = "Bit 7 - Reverse output data value in bit order"]
    #[inline(always)]
    #[must_use]
    pub fn rev_o(&mut self) -> RevOW<CtlSpec> {
        RevOW::new(self, 7)
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
#[doc = "`reset()` method sets CTL to value 0"]
impl crate::Resettable for CtlSpec {
    const RESET_VALUE: u32 = 0;
}
