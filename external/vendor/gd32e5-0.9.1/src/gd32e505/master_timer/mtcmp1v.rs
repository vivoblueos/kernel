#[doc = "Register `MTCMP1V` reader"]
pub type R = crate::R<Mtcmp1vSpec>;
#[doc = "Register `MTCMP1V` writer"]
pub type W = crate::W<Mtcmp1vSpec>;
#[doc = "Field `CMP1VAL` reader - Compare 1 value"]
pub type Cmp1valR = crate::FieldReader<u16>;
#[doc = "Field `CMP1VAL` writer - Compare 1 value"]
pub type Cmp1valW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - Compare 1 value"]
    #[inline(always)]
    pub fn cmp1val(&self) -> Cmp1valR {
        Cmp1valR::new((self.bits & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - Compare 1 value"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1val(&mut self) -> Cmp1valW<Mtcmp1vSpec> {
        Cmp1valW::new(self, 0)
    }
}
#[doc = "SHRTIMER Master_TIMER compare 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtcmp1v::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtcmp1v::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Mtcmp1vSpec;
impl crate::RegisterSpec for Mtcmp1vSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mtcmp1v::R`](R) reader structure"]
impl crate::Readable for Mtcmp1vSpec {}
#[doc = "`write(|w| ..)` method takes [`mtcmp1v::W`](W) writer structure"]
impl crate::Writable for Mtcmp1vSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MTCMP1V to value 0"]
impl crate::Resettable for Mtcmp1vSpec {
    const RESET_VALUE: u32 = 0;
}
