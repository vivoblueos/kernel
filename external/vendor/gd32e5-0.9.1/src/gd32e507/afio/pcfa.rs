#[doc = "Register `PCFA` reader"]
pub type R = crate::R<PcfaSpec>;
#[doc = "Register `PCFA` writer"]
pub type W = crate::W<PcfaSpec>;
#[doc = "Field `PA2_AFCFG` reader - PA2 AF function configuration bitse"]
pub type Pa2AfcfgR = crate::BitReader;
#[doc = "Field `PA2_AFCFG` writer - PA2 AF function configuration bitse"]
pub type Pa2AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PA3_AFCFG` reader - PA3 AF function configuration bitse"]
pub type Pa3AfcfgR = crate::BitReader;
#[doc = "Field `PA3_AFCFG` writer - PA3 AF function configuration bitse"]
pub type Pa3AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PA5_AFCFG` reader - PA5 AF function configuration bitse"]
pub type Pa5AfcfgR = crate::BitReader;
#[doc = "Field `PA5_AFCFG` writer - PA5 AF function configuration bitse"]
pub type Pa5AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PA8_AFCFG` reader - PA8 AF function configuration bitse"]
pub type Pa8AfcfgR = crate::FieldReader;
#[doc = "Field `PA8_AFCFG` writer - PA8 AF function configuration bitse"]
pub type Pa8AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PA9_AFCFG` reader - PA9 AF function configuration bitse"]
pub type Pa9AfcfgR = crate::FieldReader;
#[doc = "Field `PA9_AFCFG` writer - PA9 AF function configuration bitse"]
pub type Pa9AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PA10_AFCFG` reader - PA10 AF function configuration bitse"]
pub type Pa10AfcfgR = crate::FieldReader;
#[doc = "Field `PA10_AFCFG` writer - PA10 AF function configuration bitse"]
pub type Pa10AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PA11_AFCFG` reader - PA11 AF function configuration bitse"]
pub type Pa11AfcfgR = crate::FieldReader;
#[doc = "Field `PA11_AFCFG` writer - PA11 AF function configuration bitse"]
pub type Pa11AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PA12_AFCFG` reader - PA12 AF function configuration bitse"]
pub type Pa12AfcfgR = crate::FieldReader;
#[doc = "Field `PA12_AFCFG` writer - PA12 AF function configuration bitse"]
pub type Pa12AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PA15_AFCFG` reader - PA15 AF function configuration bit"]
pub type Pa15AfcfgR = crate::BitReader;
#[doc = "Field `PA15_AFCFG` writer - PA15 AF function configuration bit"]
pub type Pa15AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 4 - PA2 AF function configuration bitse"]
    #[inline(always)]
    pub fn pa2_afcfg(&self) -> Pa2AfcfgR {
        Pa2AfcfgR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 6 - PA3 AF function configuration bitse"]
    #[inline(always)]
    pub fn pa3_afcfg(&self) -> Pa3AfcfgR {
        Pa3AfcfgR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 10 - PA5 AF function configuration bitse"]
    #[inline(always)]
    pub fn pa5_afcfg(&self) -> Pa5AfcfgR {
        Pa5AfcfgR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bits 16:17 - PA8 AF function configuration bitse"]
    #[inline(always)]
    pub fn pa8_afcfg(&self) -> Pa8AfcfgR {
        Pa8AfcfgR::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 18:19 - PA9 AF function configuration bitse"]
    #[inline(always)]
    pub fn pa9_afcfg(&self) -> Pa9AfcfgR {
        Pa9AfcfgR::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bits 20:21 - PA10 AF function configuration bitse"]
    #[inline(always)]
    pub fn pa10_afcfg(&self) -> Pa10AfcfgR {
        Pa10AfcfgR::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bits 22:23 - PA11 AF function configuration bitse"]
    #[inline(always)]
    pub fn pa11_afcfg(&self) -> Pa11AfcfgR {
        Pa11AfcfgR::new(((self.bits >> 22) & 3) as u8)
    }
    #[doc = "Bits 24:25 - PA12 AF function configuration bitse"]
    #[inline(always)]
    pub fn pa12_afcfg(&self) -> Pa12AfcfgR {
        Pa12AfcfgR::new(((self.bits >> 24) & 3) as u8)
    }
    #[doc = "Bit 30 - PA15 AF function configuration bit"]
    #[inline(always)]
    pub fn pa15_afcfg(&self) -> Pa15AfcfgR {
        Pa15AfcfgR::new(((self.bits >> 30) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 4 - PA2 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pa2_afcfg(&mut self) -> Pa2AfcfgW<PcfaSpec> {
        Pa2AfcfgW::new(self, 4)
    }
    #[doc = "Bit 6 - PA3 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pa3_afcfg(&mut self) -> Pa3AfcfgW<PcfaSpec> {
        Pa3AfcfgW::new(self, 6)
    }
    #[doc = "Bit 10 - PA5 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pa5_afcfg(&mut self) -> Pa5AfcfgW<PcfaSpec> {
        Pa5AfcfgW::new(self, 10)
    }
    #[doc = "Bits 16:17 - PA8 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pa8_afcfg(&mut self) -> Pa8AfcfgW<PcfaSpec> {
        Pa8AfcfgW::new(self, 16)
    }
    #[doc = "Bits 18:19 - PA9 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pa9_afcfg(&mut self) -> Pa9AfcfgW<PcfaSpec> {
        Pa9AfcfgW::new(self, 18)
    }
    #[doc = "Bits 20:21 - PA10 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pa10_afcfg(&mut self) -> Pa10AfcfgW<PcfaSpec> {
        Pa10AfcfgW::new(self, 20)
    }
    #[doc = "Bits 22:23 - PA11 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pa11_afcfg(&mut self) -> Pa11AfcfgW<PcfaSpec> {
        Pa11AfcfgW::new(self, 22)
    }
    #[doc = "Bits 24:25 - PA12 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pa12_afcfg(&mut self) -> Pa12AfcfgW<PcfaSpec> {
        Pa12AfcfgW::new(self, 24)
    }
    #[doc = "Bit 30 - PA15 AF function configuration bit"]
    #[inline(always)]
    #[must_use]
    pub fn pa15_afcfg(&mut self) -> Pa15AfcfgW<PcfaSpec> {
        Pa15AfcfgW::new(self, 30)
    }
}
#[doc = "AFIO port configuration register A\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pcfa::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pcfa::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PcfaSpec;
impl crate::RegisterSpec for PcfaSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pcfa::R`](R) reader structure"]
impl crate::Readable for PcfaSpec {}
#[doc = "`write(|w| ..)` method takes [`pcfa::W`](W) writer structure"]
impl crate::Writable for PcfaSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PCFA to value 0"]
impl crate::Resettable for PcfaSpec {
    const RESET_VALUE: u32 = 0;
}
