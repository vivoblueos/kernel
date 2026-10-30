#[doc = "Register `FCTL` reader"]
pub type R = crate::R<FctlSpec>;
#[doc = "Register `FCTL` writer"]
pub type W = crate::W<FctlSpec>;
#[doc = "Field `FLD` reader - Filter lock disable"]
pub type FldR = crate::BitReader;
#[doc = "Field `FLD` writer - Filter lock disable"]
pub type FldW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Filter lock disable"]
    #[inline(always)]
    pub fn fld(&self) -> FldR {
        FldR::new((self.bits & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Filter lock disable"]
    #[inline(always)]
    #[must_use]
    pub fn fld(&mut self) -> FldW<FctlSpec> {
        FldW::new(self, 0)
    }
}
#[doc = "Filter control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FctlSpec;
impl crate::RegisterSpec for FctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fctl::R`](R) reader structure"]
impl crate::Readable for FctlSpec {}
#[doc = "`write(|w| ..)` method takes [`fctl::W`](W) writer structure"]
impl crate::Writable for FctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets FCTL to value 0x2a1c_0e01"]
impl crate::Resettable for FctlSpec {
    const RESET_VALUE: u32 = 0x2a1c_0e01;
}
