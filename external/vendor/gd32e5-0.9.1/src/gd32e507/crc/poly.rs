#[doc = "Register `POLY` reader"]
pub type R = crate::R<PolySpec>;
#[doc = "Register `POLY` writer"]
pub type W = crate::W<PolySpec>;
#[doc = "Field `POLY` reader - User configurable polynomial value"]
pub type PolyR = crate::FieldReader<u32>;
#[doc = "Field `POLY` writer - User configurable polynomial value"]
pub type PolyW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - User configurable polynomial value"]
    #[inline(always)]
    pub fn poly(&self) -> PolyR {
        PolyR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - User configurable polynomial value"]
    #[inline(always)]
    #[must_use]
    pub fn poly(&mut self) -> PolyW<PolySpec> {
        PolyW::new(self, 0)
    }
}
#[doc = "Polynomial register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`poly::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`poly::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PolySpec;
impl crate::RegisterSpec for PolySpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`poly::R`](R) reader structure"]
impl crate::Readable for PolySpec {}
#[doc = "`write(|w| ..)` method takes [`poly::W`](W) writer structure"]
impl crate::Writable for PolySpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets POLY to value 0x04c1_1db7"]
impl crate::Resettable for PolySpec {
    const RESET_VALUE: u32 = 0x04c1_1db7;
}
