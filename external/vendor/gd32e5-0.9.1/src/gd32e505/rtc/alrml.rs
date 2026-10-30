#[doc = "Register `ALRML` writer"]
pub type W = crate::W<AlrmlSpec>;
#[doc = "Field `ALRM` writer - alarm value low"]
pub type AlrmW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl W {
    #[doc = "Bits 0:15 - alarm value low"]
    #[inline(always)]
    #[must_use]
    pub fn alrm(&mut self) -> AlrmW<AlrmlSpec> {
        AlrmW::new(self, 0)
    }
}
#[doc = "RTC alarm low register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`alrml::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AlrmlSpec;
impl crate::RegisterSpec for AlrmlSpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`alrml::W`](W) writer structure"]
impl crate::Writable for AlrmlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ALRML to value 0xffff"]
impl crate::Resettable for AlrmlSpec {
    const RESET_VALUE: u32 = 0xffff;
}
