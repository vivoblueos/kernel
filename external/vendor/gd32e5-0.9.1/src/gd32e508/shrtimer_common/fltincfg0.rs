#[doc = "Register `FLTINCFG0` reader"]
pub type R = crate::R<Fltincfg0Spec>;
#[doc = "Register `FLTINCFG0` writer"]
pub type W = crate::W<Fltincfg0Spec>;
#[doc = "Field `FLT0INEN` reader - Fault 0 input enable"]
pub type Flt0inenR = crate::BitReader;
#[doc = "Field `FLT0INEN` writer - Fault 0 input enable"]
pub type Flt0inenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT0INP` reader - Fault 0 input polarity"]
pub type Flt0inpR = crate::BitReader;
#[doc = "Field `FLT0INP` writer - Fault 0 input polarity"]
pub type Flt0inpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT0INSRC` reader - Fault 0 input source"]
pub type Flt0insrcR = crate::BitReader;
#[doc = "Field `FLT0INSRC` writer - Fault 0 input source"]
pub type Flt0insrcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT0INFC` reader - Fault 0 input filter control"]
pub type Flt0infcR = crate::FieldReader;
#[doc = "Field `FLT0INFC` writer - Fault 0 input filter control"]
pub type Flt0infcW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `FLT0INPROT` reader - Protect fault 0 input configuration"]
pub type Flt0inprotR = crate::BitReader;
#[doc = "Field `FLT0INPROT` writer - Protect fault 0 input configuration"]
pub type Flt0inprotW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT1INEN` reader - Fault 1 input enable"]
pub type Flt1inenR = crate::BitReader;
#[doc = "Field `FLT1INEN` writer - Fault 1 input enable"]
pub type Flt1inenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT1INP` reader - Fault 1 input polarity"]
pub type Flt1inpR = crate::BitReader;
#[doc = "Field `FLT1INP` writer - Fault 1 input polarity"]
pub type Flt1inpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT1INSRC` reader - Fault 2 input source"]
pub type Flt1insrcR = crate::BitReader;
#[doc = "Field `FLT1INSRC` writer - Fault 2 input source"]
pub type Flt1insrcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT1INFC` reader - Fault 1 input filter control"]
pub type Flt1infcR = crate::FieldReader;
#[doc = "Field `FLT1INFC` writer - Fault 1 input filter control"]
pub type Flt1infcW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `FLT1INPROT` reader - Protect fault 1 input configuration"]
pub type Flt1inprotR = crate::BitReader;
#[doc = "Field `FLT1INPROT` writer - Protect fault 1 input configuration"]
pub type Flt1inprotW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT2INEN` reader - Fault 2 input enable"]
pub type Flt2inenR = crate::BitReader;
#[doc = "Field `FLT2INEN` writer - Fault 2 input enable"]
pub type Flt2inenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT2INP` reader - Fault 2 input polarity"]
pub type Flt2inpR = crate::BitReader;
#[doc = "Field `FLT2INP` writer - Fault 2 input polarity"]
pub type Flt2inpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT2INSRC` reader - Fault 2 input source"]
pub type Flt2insrcR = crate::BitReader;
#[doc = "Field `FLT2INSRC` writer - Fault 2 input source"]
pub type Flt2insrcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT2INFC` reader - Fault 2 input filter control"]
pub type Flt2infcR = crate::FieldReader;
#[doc = "Field `FLT2INFC` writer - Fault 2 input filter control"]
pub type Flt2infcW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `FLT2INPROT` reader - Protect fault 2 input configuration"]
pub type Flt2inprotR = crate::BitReader;
#[doc = "Field `FLT2INPROT` writer - Protect fault 2 input configuration"]
pub type Flt2inprotW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT3INEN` reader - Fault 3 input enable"]
pub type Flt3inenR = crate::BitReader;
#[doc = "Field `FLT3INEN` writer - Fault 3 input enable"]
pub type Flt3inenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT3INP` reader - Fault 3 input polarity"]
pub type Flt3inpR = crate::BitReader;
#[doc = "Field `FLT3INP` writer - Fault 3 input polarity"]
pub type Flt3inpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT3INSRC` reader - Fault 3 input source"]
pub type Flt3insrcR = crate::BitReader;
#[doc = "Field `FLT3INSRC` writer - Fault 3 input source"]
pub type Flt3insrcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FLT3INFC` reader - Fault 3 input filter control"]
pub type Flt3infcR = crate::FieldReader;
#[doc = "Field `FLT3INFC` writer - Fault 3 input filter control"]
pub type Flt3infcW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `FLT3INPROT` reader - Protect fault 3 input configuration"]
pub type Flt3inprotR = crate::BitReader;
#[doc = "Field `FLT3INPROT` writer - Protect fault 3 input configuration"]
pub type Flt3inprotW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Fault 0 input enable"]
    #[inline(always)]
    pub fn flt0inen(&self) -> Flt0inenR {
        Flt0inenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Fault 0 input polarity"]
    #[inline(always)]
    pub fn flt0inp(&self) -> Flt0inpR {
        Flt0inpR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Fault 0 input source"]
    #[inline(always)]
    pub fn flt0insrc(&self) -> Flt0insrcR {
        Flt0insrcR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bits 3:6 - Fault 0 input filter control"]
    #[inline(always)]
    pub fn flt0infc(&self) -> Flt0infcR {
        Flt0infcR::new(((self.bits >> 3) & 0x0f) as u8)
    }
    #[doc = "Bit 7 - Protect fault 0 input configuration"]
    #[inline(always)]
    pub fn flt0inprot(&self) -> Flt0inprotR {
        Flt0inprotR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Fault 1 input enable"]
    #[inline(always)]
    pub fn flt1inen(&self) -> Flt1inenR {
        Flt1inenR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Fault 1 input polarity"]
    #[inline(always)]
    pub fn flt1inp(&self) -> Flt1inpR {
        Flt1inpR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Fault 2 input source"]
    #[inline(always)]
    pub fn flt1insrc(&self) -> Flt1insrcR {
        Flt1insrcR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bits 11:14 - Fault 1 input filter control"]
    #[inline(always)]
    pub fn flt1infc(&self) -> Flt1infcR {
        Flt1infcR::new(((self.bits >> 11) & 0x0f) as u8)
    }
    #[doc = "Bit 15 - Protect fault 1 input configuration"]
    #[inline(always)]
    pub fn flt1inprot(&self) -> Flt1inprotR {
        Flt1inprotR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Fault 2 input enable"]
    #[inline(always)]
    pub fn flt2inen(&self) -> Flt2inenR {
        Flt2inenR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Fault 2 input polarity"]
    #[inline(always)]
    pub fn flt2inp(&self) -> Flt2inpR {
        Flt2inpR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Fault 2 input source"]
    #[inline(always)]
    pub fn flt2insrc(&self) -> Flt2insrcR {
        Flt2insrcR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bits 19:22 - Fault 2 input filter control"]
    #[inline(always)]
    pub fn flt2infc(&self) -> Flt2infcR {
        Flt2infcR::new(((self.bits >> 19) & 0x0f) as u8)
    }
    #[doc = "Bit 23 - Protect fault 2 input configuration"]
    #[inline(always)]
    pub fn flt2inprot(&self) -> Flt2inprotR {
        Flt2inprotR::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - Fault 3 input enable"]
    #[inline(always)]
    pub fn flt3inen(&self) -> Flt3inenR {
        Flt3inenR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Fault 3 input polarity"]
    #[inline(always)]
    pub fn flt3inp(&self) -> Flt3inpR {
        Flt3inpR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Fault 3 input source"]
    #[inline(always)]
    pub fn flt3insrc(&self) -> Flt3insrcR {
        Flt3insrcR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bits 27:30 - Fault 3 input filter control"]
    #[inline(always)]
    pub fn flt3infc(&self) -> Flt3infcR {
        Flt3infcR::new(((self.bits >> 27) & 0x0f) as u8)
    }
    #[doc = "Bit 31 - Protect fault 3 input configuration"]
    #[inline(always)]
    pub fn flt3inprot(&self) -> Flt3inprotR {
        Flt3inprotR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Fault 0 input enable"]
    #[inline(always)]
    #[must_use]
    pub fn flt0inen(&mut self) -> Flt0inenW<Fltincfg0Spec> {
        Flt0inenW::new(self, 0)
    }
    #[doc = "Bit 1 - Fault 0 input polarity"]
    #[inline(always)]
    #[must_use]
    pub fn flt0inp(&mut self) -> Flt0inpW<Fltincfg0Spec> {
        Flt0inpW::new(self, 1)
    }
    #[doc = "Bit 2 - Fault 0 input source"]
    #[inline(always)]
    #[must_use]
    pub fn flt0insrc(&mut self) -> Flt0insrcW<Fltincfg0Spec> {
        Flt0insrcW::new(self, 2)
    }
    #[doc = "Bits 3:6 - Fault 0 input filter control"]
    #[inline(always)]
    #[must_use]
    pub fn flt0infc(&mut self) -> Flt0infcW<Fltincfg0Spec> {
        Flt0infcW::new(self, 3)
    }
    #[doc = "Bit 7 - Protect fault 0 input configuration"]
    #[inline(always)]
    #[must_use]
    pub fn flt0inprot(&mut self) -> Flt0inprotW<Fltincfg0Spec> {
        Flt0inprotW::new(self, 7)
    }
    #[doc = "Bit 8 - Fault 1 input enable"]
    #[inline(always)]
    #[must_use]
    pub fn flt1inen(&mut self) -> Flt1inenW<Fltincfg0Spec> {
        Flt1inenW::new(self, 8)
    }
    #[doc = "Bit 9 - Fault 1 input polarity"]
    #[inline(always)]
    #[must_use]
    pub fn flt1inp(&mut self) -> Flt1inpW<Fltincfg0Spec> {
        Flt1inpW::new(self, 9)
    }
    #[doc = "Bit 10 - Fault 2 input source"]
    #[inline(always)]
    #[must_use]
    pub fn flt1insrc(&mut self) -> Flt1insrcW<Fltincfg0Spec> {
        Flt1insrcW::new(self, 10)
    }
    #[doc = "Bits 11:14 - Fault 1 input filter control"]
    #[inline(always)]
    #[must_use]
    pub fn flt1infc(&mut self) -> Flt1infcW<Fltincfg0Spec> {
        Flt1infcW::new(self, 11)
    }
    #[doc = "Bit 15 - Protect fault 1 input configuration"]
    #[inline(always)]
    #[must_use]
    pub fn flt1inprot(&mut self) -> Flt1inprotW<Fltincfg0Spec> {
        Flt1inprotW::new(self, 15)
    }
    #[doc = "Bit 16 - Fault 2 input enable"]
    #[inline(always)]
    #[must_use]
    pub fn flt2inen(&mut self) -> Flt2inenW<Fltincfg0Spec> {
        Flt2inenW::new(self, 16)
    }
    #[doc = "Bit 17 - Fault 2 input polarity"]
    #[inline(always)]
    #[must_use]
    pub fn flt2inp(&mut self) -> Flt2inpW<Fltincfg0Spec> {
        Flt2inpW::new(self, 17)
    }
    #[doc = "Bit 18 - Fault 2 input source"]
    #[inline(always)]
    #[must_use]
    pub fn flt2insrc(&mut self) -> Flt2insrcW<Fltincfg0Spec> {
        Flt2insrcW::new(self, 18)
    }
    #[doc = "Bits 19:22 - Fault 2 input filter control"]
    #[inline(always)]
    #[must_use]
    pub fn flt2infc(&mut self) -> Flt2infcW<Fltincfg0Spec> {
        Flt2infcW::new(self, 19)
    }
    #[doc = "Bit 23 - Protect fault 2 input configuration"]
    #[inline(always)]
    #[must_use]
    pub fn flt2inprot(&mut self) -> Flt2inprotW<Fltincfg0Spec> {
        Flt2inprotW::new(self, 23)
    }
    #[doc = "Bit 24 - Fault 3 input enable"]
    #[inline(always)]
    #[must_use]
    pub fn flt3inen(&mut self) -> Flt3inenW<Fltincfg0Spec> {
        Flt3inenW::new(self, 24)
    }
    #[doc = "Bit 25 - Fault 3 input polarity"]
    #[inline(always)]
    #[must_use]
    pub fn flt3inp(&mut self) -> Flt3inpW<Fltincfg0Spec> {
        Flt3inpW::new(self, 25)
    }
    #[doc = "Bit 26 - Fault 3 input source"]
    #[inline(always)]
    #[must_use]
    pub fn flt3insrc(&mut self) -> Flt3insrcW<Fltincfg0Spec> {
        Flt3insrcW::new(self, 26)
    }
    #[doc = "Bits 27:30 - Fault 3 input filter control"]
    #[inline(always)]
    #[must_use]
    pub fn flt3infc(&mut self) -> Flt3infcW<Fltincfg0Spec> {
        Flt3infcW::new(self, 27)
    }
    #[doc = "Bit 31 - Protect fault 3 input configuration"]
    #[inline(always)]
    #[must_use]
    pub fn flt3inprot(&mut self) -> Flt3inprotW<Fltincfg0Spec> {
        Flt3inprotW::new(self, 31)
    }
}
#[doc = "SHRTIMER fault input configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fltincfg0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fltincfg0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Fltincfg0Spec;
impl crate::RegisterSpec for Fltincfg0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fltincfg0::R`](R) reader structure"]
impl crate::Readable for Fltincfg0Spec {}
#[doc = "`write(|w| ..)` method takes [`fltincfg0::W`](W) writer structure"]
impl crate::Writable for Fltincfg0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets FLTINCFG0 to value 0"]
impl crate::Resettable for Fltincfg0Spec {
    const RESET_VALUE: u32 = 0;
}
