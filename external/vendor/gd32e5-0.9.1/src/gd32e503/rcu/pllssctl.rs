#[doc = "Register `PLLSSCTL` reader"]
pub type R = crate::R<PllssctlSpec>;
#[doc = "Register `PLLSSCTL` writer"]
pub type W = crate::W<PllssctlSpec>;
#[doc = "Field `MODCNT` reader - Configure PLL spread spectrum modulation profile amplitude and frequency"]
pub type ModcntR = crate::FieldReader<u16>;
#[doc = "Field `MODCNT` writer - Configure PLL spread spectrum modulation profile amplitude and frequency"]
pub type ModcntW<'a, REG> = crate::FieldWriter<'a, REG, 13, u16>;
#[doc = "Field `MODSTEP` reader - Configure PLL spread spectrum modulation profile amplitude and frequency"]
pub type ModstepR = crate::FieldReader<u16>;
#[doc = "Field `MODSTEP` writer - Configure PLL spread spectrum modulation profile amplitude and frequency"]
pub type ModstepW<'a, REG> = crate::FieldWriter<'a, REG, 15, u16>;
#[doc = "Field `SS_TYPE` reader - PLL spread spectrum modulation type select"]
pub type SsTypeR = crate::BitReader;
#[doc = "Field `SS_TYPE` writer - PLL spread spectrum modulation type select"]
pub type SsTypeW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SSCGON` reader - PLL spread spectrum modulation enable"]
pub type SscgonR = crate::BitReader;
#[doc = "Field `SSCGON` writer - PLL spread spectrum modulation enable"]
pub type SscgonW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:12 - Configure PLL spread spectrum modulation profile amplitude and frequency"]
    #[inline(always)]
    pub fn modcnt(&self) -> ModcntR {
        ModcntR::new((self.bits & 0x1fff) as u16)
    }
    #[doc = "Bits 13:27 - Configure PLL spread spectrum modulation profile amplitude and frequency"]
    #[inline(always)]
    pub fn modstep(&self) -> ModstepR {
        ModstepR::new(((self.bits >> 13) & 0x7fff) as u16)
    }
    #[doc = "Bit 30 - PLL spread spectrum modulation type select"]
    #[inline(always)]
    pub fn ss_type(&self) -> SsTypeR {
        SsTypeR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - PLL spread spectrum modulation enable"]
    #[inline(always)]
    pub fn sscgon(&self) -> SscgonR {
        SscgonR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:12 - Configure PLL spread spectrum modulation profile amplitude and frequency"]
    #[inline(always)]
    #[must_use]
    pub fn modcnt(&mut self) -> ModcntW<PllssctlSpec> {
        ModcntW::new(self, 0)
    }
    #[doc = "Bits 13:27 - Configure PLL spread spectrum modulation profile amplitude and frequency"]
    #[inline(always)]
    #[must_use]
    pub fn modstep(&mut self) -> ModstepW<PllssctlSpec> {
        ModstepW::new(self, 13)
    }
    #[doc = "Bit 30 - PLL spread spectrum modulation type select"]
    #[inline(always)]
    #[must_use]
    pub fn ss_type(&mut self) -> SsTypeW<PllssctlSpec> {
        SsTypeW::new(self, 30)
    }
    #[doc = "Bit 31 - PLL spread spectrum modulation enable"]
    #[inline(always)]
    #[must_use]
    pub fn sscgon(&mut self) -> SscgonW<PllssctlSpec> {
        SscgonW::new(self, 31)
    }
}
#[doc = "PLL clock spread spectrum control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pllssctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pllssctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PllssctlSpec;
impl crate::RegisterSpec for PllssctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pllssctl::R`](R) reader structure"]
impl crate::Readable for PllssctlSpec {}
#[doc = "`write(|w| ..)` method takes [`pllssctl::W`](W) writer structure"]
impl crate::Writable for PllssctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PLLSSCTL to value 0"]
impl crate::Resettable for PllssctlSpec {
    const RESET_VALUE: u32 = 0;
}
