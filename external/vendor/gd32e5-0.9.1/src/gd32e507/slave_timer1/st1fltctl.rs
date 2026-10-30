#[doc = "Register `ST1FLTCTL` reader"]
pub type R = crate::R<St1fltctlSpec>;
#[doc = "Register `ST1FLTCTL` writer"]
pub type W = crate::W<St1fltctlSpec>;
#[doc = "Field `FLT0EN` reader - Fault 0 enable"]
pub type Flt0enR = crate::BitReader;
#[doc = "Field `FLT0EN` writer - Fault 0 enable"]
pub type Flt0enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT1EN` reader - Fault 1 enable"]
pub type Flt1enR = crate::BitReader;
#[doc = "Field `FLT1EN` writer - Fault 1 enable"]
pub type Flt1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT2EN` reader - Fault 2 enable"]
pub type Flt2enR = crate::BitReader;
#[doc = "Field `FLT2EN` writer - Fault 2 enable"]
pub type Flt2enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT3EN` reader - Fault 3 enable"]
pub type Flt3enR = crate::BitReader;
#[doc = "Field `FLT3EN` writer - Fault 3 enable"]
pub type Flt3enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT4EN` reader - Fault 4 enable"]
pub type Flt4enR = crate::BitReader;
#[doc = "Field `FLT4EN` writer - Fault 4 enable"]
pub type Flt4enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLTENPROT` reader - Protect fault enable"]
pub type FltenprotR = crate::BitReader;
#[doc = "Field `FLTENPROT` writer - Protect fault enable"]
pub type FltenprotW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Fault 0 enable"]
    #[inline(always)]
    pub fn flt0en(&self) -> Flt0enR {
        Flt0enR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Fault 1 enable"]
    #[inline(always)]
    pub fn flt1en(&self) -> Flt1enR {
        Flt1enR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Fault 2 enable"]
    #[inline(always)]
    pub fn flt2en(&self) -> Flt2enR {
        Flt2enR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Fault 3 enable"]
    #[inline(always)]
    pub fn flt3en(&self) -> Flt3enR {
        Flt3enR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Fault 4 enable"]
    #[inline(always)]
    pub fn flt4en(&self) -> Flt4enR {
        Flt4enR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 31 - Protect fault enable"]
    #[inline(always)]
    pub fn fltenprot(&self) -> FltenprotR {
        FltenprotR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Fault 0 enable"]
    #[inline(always)]
    #[must_use]
    pub fn flt0en(&mut self) -> Flt0enW<St1fltctlSpec> {
        Flt0enW::new(self, 0)
    }
    #[doc = "Bit 1 - Fault 1 enable"]
    #[inline(always)]
    #[must_use]
    pub fn flt1en(&mut self) -> Flt1enW<St1fltctlSpec> {
        Flt1enW::new(self, 1)
    }
    #[doc = "Bit 2 - Fault 2 enable"]
    #[inline(always)]
    #[must_use]
    pub fn flt2en(&mut self) -> Flt2enW<St1fltctlSpec> {
        Flt2enW::new(self, 2)
    }
    #[doc = "Bit 3 - Fault 3 enable"]
    #[inline(always)]
    #[must_use]
    pub fn flt3en(&mut self) -> Flt3enW<St1fltctlSpec> {
        Flt3enW::new(self, 3)
    }
    #[doc = "Bit 4 - Fault 4 enable"]
    #[inline(always)]
    #[must_use]
    pub fn flt4en(&mut self) -> Flt4enW<St1fltctlSpec> {
        Flt4enW::new(self, 4)
    }
    #[doc = "Bit 31 - Protect fault enable"]
    #[inline(always)]
    #[must_use]
    pub fn fltenprot(&mut self) -> FltenprotW<St1fltctlSpec> {
        FltenprotW::new(self, 31)
    }
}
#[doc = "SHRTIMER Slave_TIMERx fault control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1fltctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1fltctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St1fltctlSpec;
impl crate::RegisterSpec for St1fltctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st1fltctl::R`](R) reader structure"]
impl crate::Readable for St1fltctlSpec {}
#[doc = "`write(|w| ..)` method takes [`st1fltctl::W`](W) writer structure"]
impl crate::Writable for St1fltctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST1FLTCTL to value 0"]
impl crate::Resettable for St1fltctlSpec {
    const RESET_VALUE: u32 = 0;
}
