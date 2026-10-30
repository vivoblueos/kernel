#[doc = "Register `MTCMP2V` reader"]
pub type R = crate::R<Mtcmp2vSpec>;
#[doc = "Register `MTCMP2V` writer"]
pub type W = crate::W<Mtcmp2vSpec>;
#[doc = "Field `CMP2VAL` reader - Compare 2 value"]
pub type Cmp2valR = crate::FieldReader<u16>;
#[doc = "Field `CMP2VAL` writer - Compare 2 value"]
pub type Cmp2valW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - Compare 2 value"]
    #[inline(always)]
    pub fn cmp2val(&self) -> Cmp2valR {
        Cmp2valR::new((self.bits & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - Compare 2 value"]
    #[inline(always)]
    #[must_use]
    pub fn cmp2val(&mut self) -> Cmp2valW<Mtcmp2vSpec> {
        Cmp2valW::new(self, 0)
    }
}
#[doc = "SHRTIMER Master_TIMER compare 2 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtcmp2v::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtcmp2v::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Mtcmp2vSpec;
impl crate::RegisterSpec for Mtcmp2vSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mtcmp2v::R`](R) reader structure"]
impl crate::Readable for Mtcmp2vSpec {}
#[doc = "`write(|w| ..)` method takes [`mtcmp2v::W`](W) writer structure"]
impl crate::Writable for Mtcmp2vSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MTCMP2V to value 0"]
impl crate::Resettable for Mtcmp2vSpec {
    const RESET_VALUE: u32 = 0;
}
