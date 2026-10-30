#[doc = "Register `ST3CMP0CP` reader"]
pub type R = crate::R<St3cmp0cpSpec>;
#[doc = "Register `ST3CMP0CP` writer"]
pub type W = crate::W<St3cmp0cpSpec>;
#[doc = "Field `CMP0VAL` reader - Compare 0 value"]
pub type Cmp0valR = crate::FieldReader<u16>;
#[doc = "Field `CMP0VAL` writer - Compare 0 value"]
pub type Cmp0valW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `CREP` reader - Counter repetition value"]
pub type CrepR = crate::FieldReader;
#[doc = "Field `CREP` writer - Counter repetition value"]
pub type CrepW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:15 - Compare 0 value"]
    #[inline(always)]
    pub fn cmp0val(&self) -> Cmp0valR {
        Cmp0valR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:23 - Counter repetition value"]
    #[inline(always)]
    pub fn crep(&self) -> CrepR {
        CrepR::new(((self.bits >> 16) & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:15 - Compare 0 value"]
    #[inline(always)]
    #[must_use]
    pub fn cmp0val(&mut self) -> Cmp0valW<St3cmp0cpSpec> {
        Cmp0valW::new(self, 0)
    }
    #[doc = "Bits 16:23 - Counter repetition value"]
    #[inline(always)]
    #[must_use]
    pub fn crep(&mut self) -> CrepW<St3cmp0cpSpec> {
        CrepW::new(self, 16)
    }
}
#[doc = "SHRTIMER Slave_TIMERx compare 0 composite register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cmp0cp::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cmp0cp::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St3cmp0cpSpec;
impl crate::RegisterSpec for St3cmp0cpSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st3cmp0cp::R`](R) reader structure"]
impl crate::Readable for St3cmp0cpSpec {}
#[doc = "`write(|w| ..)` method takes [`st3cmp0cp::W`](W) writer structure"]
impl crate::Writable for St3cmp0cpSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST3CMP0CP to value 0"]
impl crate::Resettable for St3cmp0cpSpec {
    const RESET_VALUE: u32 = 0;
}
