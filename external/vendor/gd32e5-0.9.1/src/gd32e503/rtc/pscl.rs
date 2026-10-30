#[doc = "Register `PSCL` writer"]
pub type W = crate::W<PsclSpec>;
#[doc = "Field `PSC` writer - RTC prescaler value low"]
pub type PscW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl W {
    #[doc = "Bits 0:15 - RTC prescaler value low"]
    #[inline(always)]
    #[must_use]
    pub fn psc(&mut self) -> PscW<PsclSpec> {
        PscW::new(self, 0)
    }
}
#[doc = "RTC prescaler low register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pscl::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PsclSpec;
impl crate::RegisterSpec for PsclSpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`pscl::W`](W) writer structure"]
impl crate::Writable for PsclSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PSCL to value 0x8000"]
impl crate::Resettable for PsclSpec {
    const RESET_VALUE: u32 = 0x8000;
}
