#[doc = "Register `TIMEOUT` reader"]
pub type R = crate::R<TimeoutSpec>;
#[doc = "Register `TIMEOUT` writer"]
pub type W = crate::W<TimeoutSpec>;
#[doc = "Field `BUSTOA` reader - Bus timeout A"]
pub type BustoaR = crate::FieldReader<u16>;
#[doc = "Field `BUSTOA` writer - Bus timeout A"]
pub type BustoaW<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
#[doc = "Field `TOIDLE` reader - Idle clock timeout detection"]
pub type ToidleR = crate::BitReader;
#[doc = "Field `TOIDLE` writer - Idle clock timeout detection"]
pub type ToidleW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TOEN` reader - Clock timeout detection enable"]
pub type ToenR = crate::BitReader;
#[doc = "Field `TOEN` writer - Clock timeout detection enable"]
pub type ToenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BUSTOB` reader - Bus timeout B"]
pub type BustobR = crate::FieldReader<u16>;
#[doc = "Field `BUSTOB` writer - Bus timeout B"]
pub type BustobW<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
#[doc = "Field `EXTOEN` reader - Extended clock timeout detection enable"]
pub type ExtoenR = crate::BitReader;
#[doc = "Field `EXTOEN` writer - Extended clock timeout detection enable"]
pub type ExtoenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:11 - Bus timeout A"]
    #[inline(always)]
    pub fn bustoa(&self) -> BustoaR {
        BustoaR::new((self.bits & 0x0fff) as u16)
    }
    #[doc = "Bit 12 - Idle clock timeout detection"]
    #[inline(always)]
    pub fn toidle(&self) -> ToidleR {
        ToidleR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 15 - Clock timeout detection enable"]
    #[inline(always)]
    pub fn toen(&self) -> ToenR {
        ToenR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 16:27 - Bus timeout B"]
    #[inline(always)]
    pub fn bustob(&self) -> BustobR {
        BustobR::new(((self.bits >> 16) & 0x0fff) as u16)
    }
    #[doc = "Bit 31 - Extended clock timeout detection enable"]
    #[inline(always)]
    pub fn extoen(&self) -> ExtoenR {
        ExtoenR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:11 - Bus timeout A"]
    #[inline(always)]
    #[must_use]
    pub fn bustoa(&mut self) -> BustoaW<TimeoutSpec> {
        BustoaW::new(self, 0)
    }
    #[doc = "Bit 12 - Idle clock timeout detection"]
    #[inline(always)]
    #[must_use]
    pub fn toidle(&mut self) -> ToidleW<TimeoutSpec> {
        ToidleW::new(self, 12)
    }
    #[doc = "Bit 15 - Clock timeout detection enable"]
    #[inline(always)]
    #[must_use]
    pub fn toen(&mut self) -> ToenW<TimeoutSpec> {
        ToenW::new(self, 15)
    }
    #[doc = "Bits 16:27 - Bus timeout B"]
    #[inline(always)]
    #[must_use]
    pub fn bustob(&mut self) -> BustobW<TimeoutSpec> {
        BustobW::new(self, 16)
    }
    #[doc = "Bit 31 - Extended clock timeout detection enable"]
    #[inline(always)]
    #[must_use]
    pub fn extoen(&mut self) -> ExtoenW<TimeoutSpec> {
        ExtoenW::new(self, 31)
    }
}
#[doc = "timeout register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`timeout::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`timeout::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TimeoutSpec;
impl crate::RegisterSpec for TimeoutSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`timeout::R`](R) reader structure"]
impl crate::Readable for TimeoutSpec {}
#[doc = "`write(|w| ..)` method takes [`timeout::W`](W) writer structure"]
impl crate::Writable for TimeoutSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets TIMEOUT to value 0"]
impl crate::Resettable for TimeoutSpec {
    const RESET_VALUE: u32 = 0;
}
