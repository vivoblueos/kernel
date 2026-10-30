#[doc = "Register `FLTINCFG1` reader"]
pub type R = crate::R<Fltincfg1Spec>;
#[doc = "Register `FLTINCFG1` writer"]
pub type W = crate::W<Fltincfg1Spec>;
#[doc = "Field `FLT4INEN` reader - Fault 4 input enable"]
pub type Flt4inenR = crate::BitReader;
#[doc = "Field `FLT4INEN` writer - Fault 4 input enable"]
pub type Flt4inenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT4INP` reader - Fault 4 input polarity"]
pub type Flt4inpR = crate::BitReader;
#[doc = "Field `FLT4INP` writer - Fault 4 input polarity"]
pub type Flt4inpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT4INSRC` reader - Fault 4 input source"]
pub type Flt4insrcR = crate::BitReader;
#[doc = "Field `FLT4INSRC` writer - Fault 4 input source"]
pub type Flt4insrcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT4INFC` reader - Fault 4 input filter control"]
pub type Flt4infcR = crate::FieldReader;
#[doc = "Field `FLT4INFC` writer - Fault 4 input filter control"]
pub type Flt4infcW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `FLT4INPROT` reader - Protect fault 4 input configuration"]
pub type Flt4inprotR = crate::BitReader;
#[doc = "Field `FLT4INPROT` writer - Protect fault 4 input configuration"]
pub type Flt4inprotW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLTFDIV` reader - Fault input digital filter clock division"]
pub type FltfdivR = crate::FieldReader;
#[doc = "Field `FLTFDIV` writer - Fault input digital filter clock division"]
pub type FltfdivW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bit 0 - Fault 4 input enable"]
    #[inline(always)]
    pub fn flt4inen(&self) -> Flt4inenR {
        Flt4inenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Fault 4 input polarity"]
    #[inline(always)]
    pub fn flt4inp(&self) -> Flt4inpR {
        Flt4inpR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Fault 4 input source"]
    #[inline(always)]
    pub fn flt4insrc(&self) -> Flt4insrcR {
        Flt4insrcR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bits 3:6 - Fault 4 input filter control"]
    #[inline(always)]
    pub fn flt4infc(&self) -> Flt4infcR {
        Flt4infcR::new(((self.bits >> 3) & 0x0f) as u8)
    }
    #[doc = "Bit 7 - Protect fault 4 input configuration"]
    #[inline(always)]
    pub fn flt4inprot(&self) -> Flt4inprotR {
        Flt4inprotR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 24:25 - Fault input digital filter clock division"]
    #[inline(always)]
    pub fn fltfdiv(&self) -> FltfdivR {
        FltfdivR::new(((self.bits >> 24) & 3) as u8)
    }
}
impl W {
    #[doc = "Bit 0 - Fault 4 input enable"]
    #[inline(always)]
    #[must_use]
    pub fn flt4inen(&mut self) -> Flt4inenW<Fltincfg1Spec> {
        Flt4inenW::new(self, 0)
    }
    #[doc = "Bit 1 - Fault 4 input polarity"]
    #[inline(always)]
    #[must_use]
    pub fn flt4inp(&mut self) -> Flt4inpW<Fltincfg1Spec> {
        Flt4inpW::new(self, 1)
    }
    #[doc = "Bit 2 - Fault 4 input source"]
    #[inline(always)]
    #[must_use]
    pub fn flt4insrc(&mut self) -> Flt4insrcW<Fltincfg1Spec> {
        Flt4insrcW::new(self, 2)
    }
    #[doc = "Bits 3:6 - Fault 4 input filter control"]
    #[inline(always)]
    #[must_use]
    pub fn flt4infc(&mut self) -> Flt4infcW<Fltincfg1Spec> {
        Flt4infcW::new(self, 3)
    }
    #[doc = "Bit 7 - Protect fault 4 input configuration"]
    #[inline(always)]
    #[must_use]
    pub fn flt4inprot(&mut self) -> Flt4inprotW<Fltincfg1Spec> {
        Flt4inprotW::new(self, 7)
    }
    #[doc = "Bits 24:25 - Fault input digital filter clock division"]
    #[inline(always)]
    #[must_use]
    pub fn fltfdiv(&mut self) -> FltfdivW<Fltincfg1Spec> {
        FltfdivW::new(self, 24)
    }
}
#[doc = "SHRTIMER fault input configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fltincfg1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fltincfg1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Fltincfg1Spec;
impl crate::RegisterSpec for Fltincfg1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fltincfg1::R`](R) reader structure"]
impl crate::Readable for Fltincfg1Spec {}
#[doc = "`write(|w| ..)` method takes [`fltincfg1::W`](W) writer structure"]
impl crate::Writable for Fltincfg1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets FLTINCFG1 to value 0"]
impl crate::Resettable for Fltincfg1Spec {
    const RESET_VALUE: u32 = 0;
}
