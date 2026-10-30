#[doc = "Register `EXEVDFCTL` reader"]
pub type R = crate::R<ExevdfctlSpec>;
#[doc = "Register `EXEVDFCTL` writer"]
pub type W = crate::W<ExevdfctlSpec>;
#[doc = "Field `EXEV5FC` reader - External event 5 filter control"]
pub type Exev5fcR = crate::FieldReader;
#[doc = "Field `EXEV5FC` writer - External event 5 filter control"]
pub type Exev5fcW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXEV6FC` reader - External event 6 filter control"]
pub type Exev6fcR = crate::FieldReader;
#[doc = "Field `EXEV6FC` writer - External event 6 filter control"]
pub type Exev6fcW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXEV7FC` reader - External event 7 filter control"]
pub type Exev7fcR = crate::FieldReader;
#[doc = "Field `EXEV7FC` writer - External event 7 filter control"]
pub type Exev7fcW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXEV8FC` reader - External event 8 filter control"]
pub type Exev8fcR = crate::FieldReader;
#[doc = "Field `EXEV8FC` writer - External event 8 filter control"]
pub type Exev8fcW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXEV9FC` reader - External event 9 filter control"]
pub type Exev9fcR = crate::FieldReader;
#[doc = "Field `EXEV9FC` writer - External event 9 filter control"]
pub type Exev9fcW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXEVFDIV` reader - External event digital filter clock division"]
pub type ExevfdivR = crate::FieldReader;
#[doc = "Field `EXEVFDIV` writer - External event digital filter clock division"]
pub type ExevfdivW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:3 - External event 5 filter control"]
    #[inline(always)]
    pub fn exev5fc(&self) -> Exev5fcR {
        Exev5fcR::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 6:9 - External event 6 filter control"]
    #[inline(always)]
    pub fn exev6fc(&self) -> Exev6fcR {
        Exev6fcR::new(((self.bits >> 6) & 0x0f) as u8)
    }
    #[doc = "Bits 12:15 - External event 7 filter control"]
    #[inline(always)]
    pub fn exev7fc(&self) -> Exev7fcR {
        Exev7fcR::new(((self.bits >> 12) & 0x0f) as u8)
    }
    #[doc = "Bits 18:21 - External event 8 filter control"]
    #[inline(always)]
    pub fn exev8fc(&self) -> Exev8fcR {
        Exev8fcR::new(((self.bits >> 18) & 0x0f) as u8)
    }
    #[doc = "Bits 24:27 - External event 9 filter control"]
    #[inline(always)]
    pub fn exev9fc(&self) -> Exev9fcR {
        Exev9fcR::new(((self.bits >> 24) & 0x0f) as u8)
    }
    #[doc = "Bits 30:31 - External event digital filter clock division"]
    #[inline(always)]
    pub fn exevfdiv(&self) -> ExevfdivR {
        ExevfdivR::new(((self.bits >> 30) & 3) as u8)
    }
}
impl W {
    #[doc = "Bits 0:3 - External event 5 filter control"]
    #[inline(always)]
    #[must_use]
    pub fn exev5fc(&mut self) -> Exev5fcW<ExevdfctlSpec> {
        Exev5fcW::new(self, 0)
    }
    #[doc = "Bits 6:9 - External event 6 filter control"]
    #[inline(always)]
    #[must_use]
    pub fn exev6fc(&mut self) -> Exev6fcW<ExevdfctlSpec> {
        Exev6fcW::new(self, 6)
    }
    #[doc = "Bits 12:15 - External event 7 filter control"]
    #[inline(always)]
    #[must_use]
    pub fn exev7fc(&mut self) -> Exev7fcW<ExevdfctlSpec> {
        Exev7fcW::new(self, 12)
    }
    #[doc = "Bits 18:21 - External event 8 filter control"]
    #[inline(always)]
    #[must_use]
    pub fn exev8fc(&mut self) -> Exev8fcW<ExevdfctlSpec> {
        Exev8fcW::new(self, 18)
    }
    #[doc = "Bits 24:27 - External event 9 filter control"]
    #[inline(always)]
    #[must_use]
    pub fn exev9fc(&mut self) -> Exev9fcW<ExevdfctlSpec> {
        Exev9fcW::new(self, 24)
    }
    #[doc = "Bits 30:31 - External event digital filter clock division"]
    #[inline(always)]
    #[must_use]
    pub fn exevfdiv(&mut self) -> ExevfdivW<ExevdfctlSpec> {
        ExevfdivW::new(self, 30)
    }
}
#[doc = "SHRTIMER external event digital filter control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`exevdfctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`exevdfctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ExevdfctlSpec;
impl crate::RegisterSpec for ExevdfctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`exevdfctl::R`](R) reader structure"]
impl crate::Readable for ExevdfctlSpec {}
#[doc = "`write(|w| ..)` method takes [`exevdfctl::W`](W) writer structure"]
impl crate::Writable for ExevdfctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets EXEVDFCTL to value 0"]
impl crate::Resettable for ExevdfctlSpec {
    const RESET_VALUE: u32 = 0;
}
