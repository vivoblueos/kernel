#[doc = "Register `ADDINT` reader"]
pub type R = crate::R<AddintSpec>;
#[doc = "Register `ADDINT` writer"]
pub type W = crate::W<AddintSpec>;
#[doc = "Field `IRC48MSTBIF` reader - IRC48M stabilization interrupt flag"]
pub type Irc48mstbifR = crate::BitReader;
#[doc = "Field `PLLUSBSTBIF` reader - PLLUSB stabilization interrupt flag"]
pub type PllusbstbifR = crate::BitReader;
#[doc = "Field `IRC48MSTBIE` reader - Internal 48 MHz RC oscillator Stabilization Interrupt Enable"]
pub type Irc48mstbieR = crate::BitReader;
#[doc = "Field `IRC48MSTBIE` writer - Internal 48 MHz RC oscillator Stabilization Interrupt Enable"]
pub type Irc48mstbieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLLUSBSTBIE` reader - PLLUSB stabilization interrupt enable"]
pub type PllusbstbieR = crate::BitReader;
#[doc = "Field `PLLUSBSTBIE` writer - PLLUSB stabilization interrupt enable"]
pub type PllusbstbieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IRC48MSTBIC` writer - Internal 48 MHz RC oscillator Stabilization Interrupt Clear"]
pub type Irc48mstbicW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLLUSBSTBIC` writer - PLLUSB stabilization interrupt clear"]
pub type PllusbstbicW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 6 - IRC48M stabilization interrupt flag"]
    #[inline(always)]
    pub fn irc48mstbif(&self) -> Irc48mstbifR {
        Irc48mstbifR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - PLLUSB stabilization interrupt flag"]
    #[inline(always)]
    pub fn pllusbstbif(&self) -> PllusbstbifR {
        PllusbstbifR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 14 - Internal 48 MHz RC oscillator Stabilization Interrupt Enable"]
    #[inline(always)]
    pub fn irc48mstbie(&self) -> Irc48mstbieR {
        Irc48mstbieR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - PLLUSB stabilization interrupt enable"]
    #[inline(always)]
    pub fn pllusbstbie(&self) -> PllusbstbieR {
        PllusbstbieR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 14 - Internal 48 MHz RC oscillator Stabilization Interrupt Enable"]
    #[inline(always)]
    #[must_use]
    pub fn irc48mstbie(&mut self) -> Irc48mstbieW<AddintSpec> {
        Irc48mstbieW::new(self, 14)
    }
    #[doc = "Bit 15 - PLLUSB stabilization interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn pllusbstbie(&mut self) -> PllusbstbieW<AddintSpec> {
        PllusbstbieW::new(self, 15)
    }
    #[doc = "Bit 22 - Internal 48 MHz RC oscillator Stabilization Interrupt Clear"]
    #[inline(always)]
    #[must_use]
    pub fn irc48mstbic(&mut self) -> Irc48mstbicW<AddintSpec> {
        Irc48mstbicW::new(self, 22)
    }
    #[doc = "Bit 23 - PLLUSB stabilization interrupt clear"]
    #[inline(always)]
    #[must_use]
    pub fn pllusbstbic(&mut self) -> PllusbstbicW<AddintSpec> {
        PllusbstbicW::new(self, 23)
    }
}
#[doc = "Additional clock interrupt register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`addint::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`addint::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AddintSpec;
impl crate::RegisterSpec for AddintSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`addint::R`](R) reader structure"]
impl crate::Readable for AddintSpec {}
#[doc = "`write(|w| ..)` method takes [`addint::W`](W) writer structure"]
impl crate::Writable for AddintSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ADDINT to value 0"]
impl crate::Resettable for AddintSpec {
    const RESET_VALUE: u32 = 0;
}
