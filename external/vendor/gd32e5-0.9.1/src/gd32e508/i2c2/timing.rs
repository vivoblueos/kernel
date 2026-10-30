#[doc = "Register `TIMING` reader"]
pub type R = crate::R<TimingSpec>;
#[doc = "Register `TIMING` writer"]
pub type W = crate::W<TimingSpec>;
#[doc = "Field `SCLL` reader - SCL low period"]
pub type ScllR = crate::FieldReader;
#[doc = "Field `SCLL` writer - SCL low period"]
pub type ScllW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SCLH` reader - SCL high period"]
pub type SclhR = crate::FieldReader;
#[doc = "Field `SCLH` writer - SCL high period"]
pub type SclhW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SDADELY` reader - Data hold time"]
pub type SdadelyR = crate::FieldReader;
#[doc = "Field `SDADELY` writer - Data hold time"]
pub type SdadelyW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `SCLDELY` reader - Data setup time"]
pub type ScldelyR = crate::FieldReader;
#[doc = "Field `SCLDELY` writer - Data setup time"]
pub type ScldelyW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `PSC` reader - Timing prescaler"]
pub type PscR = crate::FieldReader;
#[doc = "Field `PSC` writer - Timing prescaler"]
pub type PscW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:7 - SCL low period"]
    #[inline(always)]
    pub fn scll(&self) -> ScllR {
        ScllR::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - SCL high period"]
    #[inline(always)]
    pub fn sclh(&self) -> SclhR {
        SclhR::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:19 - Data hold time"]
    #[inline(always)]
    pub fn sdadely(&self) -> SdadelyR {
        SdadelyR::new(((self.bits >> 16) & 0x0f) as u8)
    }
    #[doc = "Bits 20:23 - Data setup time"]
    #[inline(always)]
    pub fn scldely(&self) -> ScldelyR {
        ScldelyR::new(((self.bits >> 20) & 0x0f) as u8)
    }
    #[doc = "Bits 28:31 - Timing prescaler"]
    #[inline(always)]
    pub fn psc(&self) -> PscR {
        PscR::new(((self.bits >> 28) & 0x0f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:7 - SCL low period"]
    #[inline(always)]
    #[must_use]
    pub fn scll(&mut self) -> ScllW<TimingSpec> {
        ScllW::new(self, 0)
    }
    #[doc = "Bits 8:15 - SCL high period"]
    #[inline(always)]
    #[must_use]
    pub fn sclh(&mut self) -> SclhW<TimingSpec> {
        SclhW::new(self, 8)
    }
    #[doc = "Bits 16:19 - Data hold time"]
    #[inline(always)]
    #[must_use]
    pub fn sdadely(&mut self) -> SdadelyW<TimingSpec> {
        SdadelyW::new(self, 16)
    }
    #[doc = "Bits 20:23 - Data setup time"]
    #[inline(always)]
    #[must_use]
    pub fn scldely(&mut self) -> ScldelyW<TimingSpec> {
        ScldelyW::new(self, 20)
    }
    #[doc = "Bits 28:31 - Timing prescaler"]
    #[inline(always)]
    #[must_use]
    pub fn psc(&mut self) -> PscW<TimingSpec> {
        PscW::new(self, 28)
    }
}
#[doc = "Timing register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`timing::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`timing::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TimingSpec;
impl crate::RegisterSpec for TimingSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`timing::R`](R) reader structure"]
impl crate::Readable for TimingSpec {}
#[doc = "`write(|w| ..)` method takes [`timing::W`](W) writer structure"]
impl crate::Writable for TimingSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets TIMING to value 0"]
impl crate::Resettable for TimingSpec {
    const RESET_VALUE: u32 = 0;
}
