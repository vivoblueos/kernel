#[doc = "Register `OVSAMPCTL` reader"]
pub type R = crate::R<OvsampctlSpec>;
#[doc = "Register `OVSAMPCTL` writer"]
pub type W = crate::W<OvsampctlSpec>;
#[doc = "Field `OVSEN` reader - Oversampling Enable"]
pub type OvsenR = crate::BitReader;
#[doc = "Field `OVSEN` writer - Oversampling Enable"]
pub type OvsenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OVSR` reader - Oversampling ratio"]
pub type OvsrR = crate::FieldReader;
#[doc = "Field `OVSR` writer - Oversampling ratio"]
pub type OvsrW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `OVSS` reader - Oversampling shift"]
pub type OvssR = crate::FieldReader;
#[doc = "Field `OVSS` writer - Oversampling shift"]
pub type OvssW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `TOVS` reader - Triggered Oversampling"]
pub type TovsR = crate::BitReader;
#[doc = "Field `TOVS` writer - Triggered Oversampling"]
pub type TovsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DRES` reader - ADC resolution"]
pub type DresR = crate::FieldReader;
#[doc = "Field `DRES` writer - ADC resolution"]
pub type DresW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bit 0 - Oversampling Enable"]
    #[inline(always)]
    pub fn ovsen(&self) -> OvsenR {
        OvsenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 2:4 - Oversampling ratio"]
    #[inline(always)]
    pub fn ovsr(&self) -> OvsrR {
        OvsrR::new(((self.bits >> 2) & 7) as u8)
    }
    #[doc = "Bits 5:8 - Oversampling shift"]
    #[inline(always)]
    pub fn ovss(&self) -> OvssR {
        OvssR::new(((self.bits >> 5) & 0x0f) as u8)
    }
    #[doc = "Bit 9 - Triggered Oversampling"]
    #[inline(always)]
    pub fn tovs(&self) -> TovsR {
        TovsR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bits 12:13 - ADC resolution"]
    #[inline(always)]
    pub fn dres(&self) -> DresR {
        DresR::new(((self.bits >> 12) & 3) as u8)
    }
}
impl W {
    #[doc = "Bit 0 - Oversampling Enable"]
    #[inline(always)]
    #[must_use]
    pub fn ovsen(&mut self) -> OvsenW<OvsampctlSpec> {
        OvsenW::new(self, 0)
    }
    #[doc = "Bits 2:4 - Oversampling ratio"]
    #[inline(always)]
    #[must_use]
    pub fn ovsr(&mut self) -> OvsrW<OvsampctlSpec> {
        OvsrW::new(self, 2)
    }
    #[doc = "Bits 5:8 - Oversampling shift"]
    #[inline(always)]
    #[must_use]
    pub fn ovss(&mut self) -> OvssW<OvsampctlSpec> {
        OvssW::new(self, 5)
    }
    #[doc = "Bit 9 - Triggered Oversampling"]
    #[inline(always)]
    #[must_use]
    pub fn tovs(&mut self) -> TovsW<OvsampctlSpec> {
        TovsW::new(self, 9)
    }
    #[doc = "Bits 12:13 - ADC resolution"]
    #[inline(always)]
    #[must_use]
    pub fn dres(&mut self) -> DresW<OvsampctlSpec> {
        DresW::new(self, 12)
    }
}
#[doc = "Oversample control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ovsampctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ovsampctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OvsampctlSpec;
impl crate::RegisterSpec for OvsampctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ovsampctl::R`](R) reader structure"]
impl crate::Readable for OvsampctlSpec {}
#[doc = "`write(|w| ..)` method takes [`ovsampctl::W`](W) writer structure"]
impl crate::Writable for OvsampctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets OVSAMPCTL to value 0"]
impl crate::Resettable for OvsampctlSpec {
    const RESET_VALUE: u32 = 0;
}
