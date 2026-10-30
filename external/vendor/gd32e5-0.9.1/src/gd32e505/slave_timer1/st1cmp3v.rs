#[doc = "Register `ST1CMP3V` reader"]
pub type R = crate::R<St1cmp3vSpec>;
#[doc = "Register `ST1CMP3V` writer"]
pub type W = crate::W<St1cmp3vSpec>;
#[doc = "Field `CMP3VAL` reader - Compare 3 value"]
pub type Cmp3valR = crate::FieldReader<u16>;
#[doc = "Field `CMP3VAL` writer - Compare 3 value"]
pub type Cmp3valW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - Compare 3 value"]
    #[inline(always)]
    pub fn cmp3val(&self) -> Cmp3valR {
        Cmp3valR::new((self.bits & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - Compare 3 value"]
    #[inline(always)]
    #[must_use]
    pub fn cmp3val(&mut self) -> Cmp3valW<St1cmp3vSpec> {
        Cmp3valW::new(self, 0)
    }
}
#[doc = "SHRTIMER Slave_TIMER1 compare 3 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1cmp3v::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1cmp3v::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St1cmp3vSpec;
impl crate::RegisterSpec for St1cmp3vSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st1cmp3v::R`](R) reader structure"]
impl crate::Readable for St1cmp3vSpec {}
#[doc = "`write(|w| ..)` method takes [`st1cmp3v::W`](W) writer structure"]
impl crate::Writable for St1cmp3vSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST1CMP3V to value 0"]
impl crate::Resettable for St1cmp3vSpec {
    const RESET_VALUE: u32 = 0;
}
