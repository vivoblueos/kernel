#[doc = "Register `BMCAR` reader"]
pub type R = crate::R<BmcarSpec>;
#[doc = "Register `BMCAR` writer"]
pub type W = crate::W<BmcarSpec>;
#[doc = "Field `BMCARL` reader - Bunch mode counter auto reload value"]
pub type BmcarlR = crate::FieldReader<u16>;
#[doc = "Field `BMCARL` writer - Bunch mode counter auto reload value"]
pub type BmcarlW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - Bunch mode counter auto reload value"]
    #[inline(always)]
    pub fn bmcarl(&self) -> BmcarlR {
        BmcarlR::new((self.bits & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - Bunch mode counter auto reload value"]
    #[inline(always)]
    #[must_use]
    pub fn bmcarl(&mut self) -> BmcarlW<BmcarSpec> {
        BmcarlW::new(self, 0)
    }
}
#[doc = "SHRTIMER bunch mode counter auto reload register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`bmcar::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bmcar::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BmcarSpec;
impl crate::RegisterSpec for BmcarSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`bmcar::R`](R) reader structure"]
impl crate::Readable for BmcarSpec {}
#[doc = "`write(|w| ..)` method takes [`bmcar::W`](W) writer structure"]
impl crate::Writable for BmcarSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets BMCAR to value 0"]
impl crate::Resettable for BmcarSpec {
    const RESET_VALUE: u32 = 0;
}
