#[doc = "Register `OBKEY` writer"]
pub type W = crate::W<ObkeySpec>;
#[doc = "Field `OBKEY` writer - FMC_ OBCTL0 option byte operation unlock register"]
pub type ObkeyW<'a, REG> = crate::FieldWriterSafe<'a, REG, 32, u32>;
impl W {
    #[doc = "Bits 0:31 - FMC_ OBCTL0 option byte operation unlock register"]
    #[inline(always)]
    #[must_use]
    pub fn obkey(&mut self) -> ObkeyW<ObkeySpec> {
        ObkeyW::new(self, 0)
    }
}
#[doc = "Option byte unlock key register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`obkey::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ObkeySpec;
impl crate::RegisterSpec for ObkeySpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`obkey::W`](W) writer structure"]
impl crate::Writable for ObkeySpec {
    type Safety = crate::Safe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets OBKEY to value 0"]
impl crate::Resettable for ObkeySpec {
    const RESET_VALUE: u32 = 0;
}
