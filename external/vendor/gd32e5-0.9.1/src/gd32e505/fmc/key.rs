#[doc = "Register `KEY` writer"]
pub type W = crate::W<KeySpec>;
#[doc = "Field `KEY` writer - FMC_CTL unlock register"]
pub type KeyW<'a, REG> = crate::FieldWriterSafe<'a, REG, 32, u32>;
impl W {
    #[doc = "Bits 0:31 - FMC_CTL unlock register"]
    #[inline(always)]
    #[must_use]
    pub fn key(&mut self) -> KeyW<KeySpec> {
        KeyW::new(self, 0)
    }
}
#[doc = "Unlock key register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`key::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct KeySpec;
impl crate::RegisterSpec for KeySpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`key::W`](W) writer structure"]
impl crate::Writable for KeySpec {
    type Safety = crate::Safe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets KEY to value 0"]
impl crate::Resettable for KeySpec {
    const RESET_VALUE: u32 = 0;
}
