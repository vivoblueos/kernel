#[doc = "Register `ST2CAP0V` reader"]
pub type R = crate::R<St2cap0vSpec>;
#[doc = "Register `ST2CAP0V` writer"]
pub type W = crate::W<St2cap0vSpec>;
#[doc = "Field `CAP0VAL` reader - Capture 0 value"]
pub type Cap0valR = crate::FieldReader<u16>;
#[doc = "Field `CAP0VAL` writer - Capture 0 value"]
pub type Cap0valW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - Capture 0 value"]
    #[inline(always)]
    pub fn cap0val(&self) -> Cap0valR {
        Cap0valR::new((self.bits & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - Capture 0 value"]
    #[inline(always)]
    #[must_use]
    pub fn cap0val(&mut self) -> Cap0valW<St2cap0vSpec> {
        Cap0valW::new(self, 0)
    }
}
#[doc = "SHRTIMER Slave_TIMERx capture 0 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2cap0v::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2cap0v::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St2cap0vSpec;
impl crate::RegisterSpec for St2cap0vSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st2cap0v::R`](R) reader structure"]
impl crate::Readable for St2cap0vSpec {}
#[doc = "`write(|w| ..)` method takes [`st2cap0v::W`](W) writer structure"]
impl crate::Writable for St2cap0vSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST2CAP0V to value 0"]
impl crate::Resettable for St2cap0vSpec {
    const RESET_VALUE: u32 = 0;
}
