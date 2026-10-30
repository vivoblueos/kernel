#[doc = "Register `BAUD` reader"]
pub type R = crate::R<BaudSpec>;
#[doc = "Register `BAUD` writer"]
pub type W = crate::W<BaudSpec>;
#[doc = "Field `FRADIV` reader - Fraction part of baud-rate divider"]
pub type FradivR = crate::FieldReader;
#[doc = "Field `FRADIV` writer - Fraction part of baud-rate divider"]
pub type FradivW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `INTDIV` reader - Integer part of baud-rate divider"]
pub type IntdivR = crate::FieldReader<u16>;
#[doc = "Field `INTDIV` writer - Integer part of baud-rate divider"]
pub type IntdivW<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
impl R {
    #[doc = "Bits 0:3 - Fraction part of baud-rate divider"]
    #[inline(always)]
    pub fn fradiv(&self) -> FradivR {
        FradivR::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:15 - Integer part of baud-rate divider"]
    #[inline(always)]
    pub fn intdiv(&self) -> IntdivR {
        IntdivR::new(((self.bits >> 4) & 0x0fff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:3 - Fraction part of baud-rate divider"]
    #[inline(always)]
    #[must_use]
    pub fn fradiv(&mut self) -> FradivW<BaudSpec> {
        FradivW::new(self, 0)
    }
    #[doc = "Bits 4:15 - Integer part of baud-rate divider"]
    #[inline(always)]
    #[must_use]
    pub fn intdiv(&mut self) -> IntdivW<BaudSpec> {
        IntdivW::new(self, 4)
    }
}
#[doc = "Baud rate register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`baud::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`baud::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BaudSpec;
impl crate::RegisterSpec for BaudSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`baud::R`](R) reader structure"]
impl crate::Readable for BaudSpec {}
#[doc = "`write(|w| ..)` method takes [`baud::W`](W) writer structure"]
impl crate::Writable for BaudSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets BAUD to value 0"]
impl crate::Resettable for BaudSpec {
    const RESET_VALUE: u32 = 0;
}
