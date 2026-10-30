#[doc = "Register `OCTL` reader"]
pub type R = crate::R<OctlSpec>;
#[doc = "Register `OCTL` writer"]
pub type W = crate::W<OctlSpec>;
#[doc = "Field `RCCV` reader - RTC clock calibration value"]
pub type RccvR = crate::FieldReader;
#[doc = "Field `RCCV` writer - RTC clock calibration value"]
pub type RccvW<'a, REG> = crate::FieldWriter<'a, REG, 7>;
#[doc = "Field `COEN` reader - RTC clock calibration output enable"]
pub type CoenR = crate::BitReader;
#[doc = "Field `COEN` writer - RTC clock calibration output enable"]
pub type CoenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ASOEN` reader - RTC alarm or second signal output enable"]
pub type AsoenR = crate::BitReader;
#[doc = "Field `ASOEN` writer - RTC alarm or second signal output enable"]
pub type AsoenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ROSEL` reader - RTC output selection"]
pub type RoselR = crate::BitReader;
#[doc = "Field `ROSEL` writer - RTC output selection"]
pub type RoselW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CCOSEL` reader - RTC clock output selection"]
pub type CcoselR = crate::BitReader;
#[doc = "Field `CCOSEL` writer - RTC clock output selection"]
pub type CcoselW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CALDIR` reader - RTC clock calibration direction"]
pub type CaldirR = crate::BitReader;
#[doc = "Field `CALDIR` writer - RTC clock calibration direction"]
pub type CaldirW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:6 - RTC clock calibration value"]
    #[inline(always)]
    pub fn rccv(&self) -> RccvR {
        RccvR::new((self.bits & 0x7f) as u8)
    }
    #[doc = "Bit 7 - RTC clock calibration output enable"]
    #[inline(always)]
    pub fn coen(&self) -> CoenR {
        CoenR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - RTC alarm or second signal output enable"]
    #[inline(always)]
    pub fn asoen(&self) -> AsoenR {
        AsoenR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - RTC output selection"]
    #[inline(always)]
    pub fn rosel(&self) -> RoselR {
        RoselR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 14 - RTC clock output selection"]
    #[inline(always)]
    pub fn ccosel(&self) -> CcoselR {
        CcoselR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - RTC clock calibration direction"]
    #[inline(always)]
    pub fn caldir(&self) -> CaldirR {
        CaldirR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:6 - RTC clock calibration value"]
    #[inline(always)]
    #[must_use]
    pub fn rccv(&mut self) -> RccvW<OctlSpec> {
        RccvW::new(self, 0)
    }
    #[doc = "Bit 7 - RTC clock calibration output enable"]
    #[inline(always)]
    #[must_use]
    pub fn coen(&mut self) -> CoenW<OctlSpec> {
        CoenW::new(self, 7)
    }
    #[doc = "Bit 8 - RTC alarm or second signal output enable"]
    #[inline(always)]
    #[must_use]
    pub fn asoen(&mut self) -> AsoenW<OctlSpec> {
        AsoenW::new(self, 8)
    }
    #[doc = "Bit 9 - RTC output selection"]
    #[inline(always)]
    #[must_use]
    pub fn rosel(&mut self) -> RoselW<OctlSpec> {
        RoselW::new(self, 9)
    }
    #[doc = "Bit 14 - RTC clock output selection"]
    #[inline(always)]
    #[must_use]
    pub fn ccosel(&mut self) -> CcoselW<OctlSpec> {
        CcoselW::new(self, 14)
    }
    #[doc = "Bit 15 - RTC clock calibration direction"]
    #[inline(always)]
    #[must_use]
    pub fn caldir(&mut self) -> CaldirW<OctlSpec> {
        CaldirW::new(self, 15)
    }
}
#[doc = "RTC signal output control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`octl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`octl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OctlSpec;
impl crate::RegisterSpec for OctlSpec {
    type Ux = u16;
}
#[doc = "`read()` method returns [`octl::R`](R) reader structure"]
impl crate::Readable for OctlSpec {}
#[doc = "`write(|w| ..)` method takes [`octl::W`](W) writer structure"]
impl crate::Writable for OctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u16 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u16 = 0;
}
#[doc = "`reset()` method sets OCTL to value 0"]
impl crate::Resettable for OctlSpec {
    const RESET_VALUE: u16 = 0;
}
