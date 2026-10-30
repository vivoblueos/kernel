#[doc = "Register `MTCREP` reader"]
pub type R = crate::R<MtcrepSpec>;
#[doc = "Register `MTCREP` writer"]
pub type W = crate::W<MtcrepSpec>;
#[doc = "Field `CREP` reader - Counter repetition value"]
pub type CrepR = crate::FieldReader;
#[doc = "Field `CREP` writer - Counter repetition value"]
pub type CrepW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - Counter repetition value"]
    #[inline(always)]
    pub fn crep(&self) -> CrepR {
        CrepR::new((self.bits & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:7 - Counter repetition value"]
    #[inline(always)]
    #[must_use]
    pub fn crep(&mut self) -> CrepW<MtcrepSpec> {
        CrepW::new(self, 0)
    }
}
#[doc = "SHRTIMER Master_TIMER counter repetition register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtcrep::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtcrep::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MtcrepSpec;
impl crate::RegisterSpec for MtcrepSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mtcrep::R`](R) reader structure"]
impl crate::Readable for MtcrepSpec {}
#[doc = "`write(|w| ..)` method takes [`mtcrep::W`](W) writer structure"]
impl crate::Writable for MtcrepSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MTCREP to value 0"]
impl crate::Resettable for MtcrepSpec {
    const RESET_VALUE: u32 = 0;
}
