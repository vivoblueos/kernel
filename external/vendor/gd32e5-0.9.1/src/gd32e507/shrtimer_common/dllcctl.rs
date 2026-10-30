#[doc = "Register `DLLCCTL` reader"]
pub type R = crate::R<DllcctlSpec>;
#[doc = "Register `DLLCCTL` writer"]
pub type W = crate::W<DllcctlSpec>;
#[doc = "Field `CLBSTRT` reader - DLL calibration start once"]
pub type ClbstrtR = crate::BitReader;
#[doc = "Field `CLBSTRT` writer - DLL calibration start once"]
pub type ClbstrtW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLBPEREN` reader - DLL periodic calibration enable"]
pub type ClbperenR = crate::BitReader;
#[doc = "Field `CLBPEREN` writer - DLL periodic calibration enable"]
pub type ClbperenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLBPER` reader - DLL calibration period"]
pub type ClbperR = crate::FieldReader;
#[doc = "Field `CLBPER` writer - DLL calibration period"]
pub type ClbperW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bit 0 - DLL calibration start once"]
    #[inline(always)]
    pub fn clbstrt(&self) -> ClbstrtR {
        ClbstrtR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - DLL periodic calibration enable"]
    #[inline(always)]
    pub fn clbperen(&self) -> ClbperenR {
        ClbperenR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:3 - DLL calibration period"]
    #[inline(always)]
    pub fn clbper(&self) -> ClbperR {
        ClbperR::new(((self.bits >> 2) & 3) as u8)
    }
}
impl W {
    #[doc = "Bit 0 - DLL calibration start once"]
    #[inline(always)]
    #[must_use]
    pub fn clbstrt(&mut self) -> ClbstrtW<DllcctlSpec> {
        ClbstrtW::new(self, 0)
    }
    #[doc = "Bit 1 - DLL periodic calibration enable"]
    #[inline(always)]
    #[must_use]
    pub fn clbperen(&mut self) -> ClbperenW<DllcctlSpec> {
        ClbperenW::new(self, 1)
    }
    #[doc = "Bits 2:3 - DLL calibration period"]
    #[inline(always)]
    #[must_use]
    pub fn clbper(&mut self) -> ClbperW<DllcctlSpec> {
        ClbperW::new(self, 2)
    }
}
#[doc = "SHRTIMER DLL calibration control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dllcctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dllcctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DllcctlSpec;
impl crate::RegisterSpec for DllcctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dllcctl::R`](R) reader structure"]
impl crate::Readable for DllcctlSpec {}
#[doc = "`write(|w| ..)` method takes [`dllcctl::W`](W) writer structure"]
impl crate::Writable for DllcctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DLLCCTL to value 0"]
impl crate::Resettable for DllcctlSpec {
    const RESET_VALUE: u32 = 0;
}
