#[doc = "Register `ST0CMP1V` reader"]
pub type R = crate::R<St0cmp1vSpec>;
#[doc = "Register `ST0CMP1V` writer"]
pub type W = crate::W<St0cmp1vSpec>;
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
    pub fn cmp1val(&mut self) -> Cmp1valW<St0cmp1vSpec> {
        Cmp1valW::new(self, 0)
    }
}
#[doc = "SHRTIMER Slave_TIMER0 compare 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cmp1v::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cmp1v::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St0cmp1vSpec;
impl crate::RegisterSpec for St0cmp1vSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st0cmp1v::R`](R) reader structure"]
impl crate::Readable for St0cmp1vSpec {}
#[doc = "`write(|w| ..)` method takes [`st0cmp1v::W`](W) writer structure"]
impl crate::Writable for St0cmp1vSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST0CMP1V to value 0"]
impl crate::Resettable for St0cmp1vSpec {
    const RESET_VALUE: u32 = 0;
}
