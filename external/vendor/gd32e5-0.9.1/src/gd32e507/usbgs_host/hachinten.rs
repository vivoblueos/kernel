#[doc = "Register `HACHINTEN` reader"]
pub type R = crate::R<HachintenSpec>;
#[doc = "Register `HACHINTEN` writer"]
pub type W = crate::W<HachintenSpec>;
#[doc = "Field `CINTEN` reader - Channel interrupt enable"]
pub type CintenR = crate::FieldReader<u16>;
#[doc = "Field `CINTEN` writer - Channel interrupt enable"]
pub type CintenW<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
impl R {
    #[doc = "Bits 0:11 - Channel interrupt enable"]
    #[inline(always)]
    pub fn cinten(&self) -> CintenR {
        CintenR::new((self.bits & 0x0fff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:11 - Channel interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cinten(&mut self) -> CintenW<HachintenSpec> {
        CintenW::new(self, 0)
    }
}
#[doc = "host all channels interrupt mask register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hachinten::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hachinten::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HachintenSpec;
impl crate::RegisterSpec for HachintenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hachinten::R`](R) reader structure"]
impl crate::Readable for HachintenSpec {}
#[doc = "`write(|w| ..)` method takes [`hachinten::W`](W) writer structure"]
impl crate::Writable for HachintenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets HACHINTEN to value 0"]
impl crate::Resettable for HachintenSpec {
    const RESET_VALUE: u32 = 0;
}
