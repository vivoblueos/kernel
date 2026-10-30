#[doc = "Register `ALRMH` writer"]
pub type W = crate::W<AlrmhSpec>;
#[doc = "Field `ALRM` writer - Alarm value high"]
pub type AlrmW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl W {
    #[doc = "Bits 0:15 - Alarm value high"]
    #[inline(always)]
    #[must_use]
    pub fn alrm(&mut self) -> AlrmW<AlrmhSpec> {
        AlrmW::new(self, 0)
    }
}
#[doc = "Alarm high register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`alrmh::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AlrmhSpec;
impl crate::RegisterSpec for AlrmhSpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`alrmh::W`](W) writer structure"]
impl crate::Writable for AlrmhSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ALRMH to value 0xffff"]
impl crate::Resettable for AlrmhSpec {
    const RESET_VALUE: u32 = 0xffff;
}
