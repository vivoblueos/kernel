#[doc = "Register `DAEPINTEN` reader"]
pub type R = crate::R<DaepintenSpec>;
#[doc = "Register `DAEPINTEN` writer"]
pub type W = crate::W<DaepintenSpec>;
#[doc = "Field `IEPIE` reader - IN EP interrupt interrupt enable bits"]
pub type IepieR = crate::FieldReader;
#[doc = "Field `IEPIE` writer - IN EP interrupt interrupt enable bits"]
pub type IepieW<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `OEPIE` reader - OUT endpoint interrupt enable bits"]
pub type OepieR = crate::FieldReader;
#[doc = "Field `OEPIE` writer - OUT endpoint interrupt enable bits"]
pub type OepieW<'a, REG> = crate::FieldWriter<'a, REG, 6>;
impl R {
    #[doc = "Bits 0:5 - IN EP interrupt interrupt enable bits"]
    #[inline(always)]
    pub fn iepie(&self) -> IepieR {
        IepieR::new((self.bits & 0x3f) as u8)
    }
    #[doc = "Bits 16:21 - OUT endpoint interrupt enable bits"]
    #[inline(always)]
    pub fn oepie(&self) -> OepieR {
        OepieR::new(((self.bits >> 16) & 0x3f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:5 - IN EP interrupt interrupt enable bits"]
    #[inline(always)]
    #[must_use]
    pub fn iepie(&mut self) -> IepieW<DaepintenSpec> {
        IepieW::new(self, 0)
    }
    #[doc = "Bits 16:21 - OUT endpoint interrupt enable bits"]
    #[inline(always)]
    #[must_use]
    pub fn oepie(&mut self) -> OepieW<DaepintenSpec> {
        OepieW::new(self, 16)
    }
}
#[doc = "Device all endpoints interrupt enable register (DAEPINTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`daepinten::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`daepinten::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DaepintenSpec;
impl crate::RegisterSpec for DaepintenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`daepinten::R`](R) reader structure"]
impl crate::Readable for DaepintenSpec {}
#[doc = "`write(|w| ..)` method takes [`daepinten::W`](W) writer structure"]
impl crate::Writable for DaepintenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DAEPINTEN to value 0"]
impl crate::Resettable for DaepintenSpec {
    const RESET_VALUE: u32 = 0;
}
