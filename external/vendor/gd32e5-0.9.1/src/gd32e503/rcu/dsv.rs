#[doc = "Register `DSV` reader"]
pub type R = crate::R<DsvSpec>;
#[doc = "Register `DSV` writer"]
pub type W = crate::W<DsvSpec>;
#[doc = "Field `DSLPVS` reader - Deep-sleep mode voltage select"]
pub type DslpvsR = crate::FieldReader;
#[doc = "Field `DSLPVS` writer - Deep-sleep mode voltage select"]
pub type DslpvsW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
impl R {
    #[doc = "Bits 0:2 - Deep-sleep mode voltage select"]
    #[inline(always)]
    pub fn dslpvs(&self) -> DslpvsR {
        DslpvsR::new((self.bits & 7) as u8)
    }
}
impl W {
    #[doc = "Bits 0:2 - Deep-sleep mode voltage select"]
    #[inline(always)]
    #[must_use]
    pub fn dslpvs(&mut self) -> DslpvsW<DsvSpec> {
        DslpvsW::new(self, 0)
    }
}
#[doc = "Deep sleep mode Voltage register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dsv::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dsv::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DsvSpec;
impl crate::RegisterSpec for DsvSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dsv::R`](R) reader structure"]
impl crate::Readable for DsvSpec {}
#[doc = "`write(|w| ..)` method takes [`dsv::W`](W) writer structure"]
impl crate::Writable for DsvSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DSV to value 0"]
impl crate::Resettable for DsvSpec {
    const RESET_VALUE: u32 = 0;
}
