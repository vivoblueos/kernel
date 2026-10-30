#[doc = "Register `INTC` writer"]
pub type W = crate::W<IntcSpec>;
#[doc = "Field `CKOKIC` writer - CKOKIF interrupt clear bit"]
pub type CkokicW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CKWARNIC` writer - CKWARNIF interrupt clear bit"]
pub type CkwarnicW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ERRIC` writer - ERRIF interrupt clear bit"]
pub type ErricW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EREFIC` writer - EREFIF interrupt clear bit"]
pub type EreficW<'a, REG> = crate::BitWriter<'a, REG>;
impl W {
    #[doc = "Bit 0 - CKOKIF interrupt clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn ckokic(&mut self) -> CkokicW<IntcSpec> {
        CkokicW::new(self, 0)
    }
    #[doc = "Bit 1 - CKWARNIF interrupt clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn ckwarnic(&mut self) -> CkwarnicW<IntcSpec> {
        CkwarnicW::new(self, 1)
    }
    #[doc = "Bit 2 - ERRIF interrupt clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn erric(&mut self) -> ErricW<IntcSpec> {
        ErricW::new(self, 2)
    }
    #[doc = "Bit 3 - EREFIF interrupt clear bit"]
    #[inline(always)]
    #[must_use]
    pub fn erefic(&mut self) -> EreficW<IntcSpec> {
        EreficW::new(self, 3)
    }
}
#[doc = "Interrupt clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`intc::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IntcSpec;
impl crate::RegisterSpec for IntcSpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`intc::W`](W) writer structure"]
impl crate::Writable for IntcSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets INTC to value 0"]
impl crate::Resettable for IntcSpec {
    const RESET_VALUE: u32 = 0;
}
