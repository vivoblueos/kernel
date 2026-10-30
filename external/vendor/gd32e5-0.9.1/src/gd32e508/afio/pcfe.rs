#[doc = "Register `PCFE` reader"]
pub type R = crate::R<PcfeSpec>;
#[doc = "Register `PCFE` writer"]
pub type W = crate::W<PcfeSpec>;
#[doc = "Field `PE0_AFCFG` reader - PE0 AF function configuration bitse"]
pub type Pe0AfcfgR = crate::FieldReader;
#[doc = "Field `PE0_AFCFG` writer - PE0 AF function configuration bitse"]
pub type Pe0AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PE1_AFCFG` reader - PE1 AF function configuration bitse"]
pub type Pe1AfcfgR = crate::FieldReader;
#[doc = "Field `PE1_AFCFG` writer - PE1 AF function configuration bitse"]
pub type Pe1AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PE8_AFCFG` reader - PE8 AF function configuration bitse"]
pub type Pe8AfcfgR = crate::FieldReader;
#[doc = "Field `PE8_AFCFG` writer - PE8 AF function configuration bitse"]
pub type Pe8AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PE9_AFCFG` reader - PE9 AF function configuration bitse"]
pub type Pe9AfcfgR = crate::FieldReader;
#[doc = "Field `PE9_AFCFG` writer - PE9 AF function configuration bitse"]
pub type Pe9AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PE10_AFCFG` reader - PE10 AF function configuration bitse"]
pub type Pe10AfcfgR = crate::BitReader;
#[doc = "Field `PE10_AFCFG` writer - PE10 AF function configuration bitse"]
pub type Pe10AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PE11_AFCFG` reader - PE11 AF function configuration bitse"]
pub type Pe11AfcfgR = crate::FieldReader;
#[doc = "Field `PE11_AFCFG` writer - PE11 AF function configuration bitse"]
pub type Pe11AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PE12_AFCFG` reader - PE12 AF function configuration bitse"]
pub type Pe12AfcfgR = crate::BitReader;
#[doc = "Field `PE12_AFCFG` writer - PE12 AF function configuration bitse"]
pub type Pe12AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PE13_AFCFG` reader - PE13 AF function configuration bitse"]
pub type Pe13AfcfgR = crate::BitReader;
#[doc = "Field `PE13_AFCFG` writer - PE13 AF function configuration bitse"]
pub type Pe13AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:1 - PE0 AF function configuration bitse"]
    #[inline(always)]
    pub fn pe0_afcfg(&self) -> Pe0AfcfgR {
        Pe0AfcfgR::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:3 - PE1 AF function configuration bitse"]
    #[inline(always)]
    pub fn pe1_afcfg(&self) -> Pe1AfcfgR {
        Pe1AfcfgR::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 16:17 - PE8 AF function configuration bitse"]
    #[inline(always)]
    pub fn pe8_afcfg(&self) -> Pe8AfcfgR {
        Pe8AfcfgR::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 18:19 - PE9 AF function configuration bitse"]
    #[inline(always)]
    pub fn pe9_afcfg(&self) -> Pe9AfcfgR {
        Pe9AfcfgR::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bit 20 - PE10 AF function configuration bitse"]
    #[inline(always)]
    pub fn pe10_afcfg(&self) -> Pe10AfcfgR {
        Pe10AfcfgR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bits 22:23 - PE11 AF function configuration bitse"]
    #[inline(always)]
    pub fn pe11_afcfg(&self) -> Pe11AfcfgR {
        Pe11AfcfgR::new(((self.bits >> 22) & 3) as u8)
    }
    #[doc = "Bit 24 - PE12 AF function configuration bitse"]
    #[inline(always)]
    pub fn pe12_afcfg(&self) -> Pe12AfcfgR {
        Pe12AfcfgR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 26 - PE13 AF function configuration bitse"]
    #[inline(always)]
    pub fn pe13_afcfg(&self) -> Pe13AfcfgR {
        Pe13AfcfgR::new(((self.bits >> 26) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:1 - PE0 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pe0_afcfg(&mut self) -> Pe0AfcfgW<PcfeSpec> {
        Pe0AfcfgW::new(self, 0)
    }
    #[doc = "Bits 2:3 - PE1 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pe1_afcfg(&mut self) -> Pe1AfcfgW<PcfeSpec> {
        Pe1AfcfgW::new(self, 2)
    }
    #[doc = "Bits 16:17 - PE8 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pe8_afcfg(&mut self) -> Pe8AfcfgW<PcfeSpec> {
        Pe8AfcfgW::new(self, 16)
    }
    #[doc = "Bits 18:19 - PE9 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pe9_afcfg(&mut self) -> Pe9AfcfgW<PcfeSpec> {
        Pe9AfcfgW::new(self, 18)
    }
    #[doc = "Bit 20 - PE10 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pe10_afcfg(&mut self) -> Pe10AfcfgW<PcfeSpec> {
        Pe10AfcfgW::new(self, 20)
    }
    #[doc = "Bits 22:23 - PE11 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pe11_afcfg(&mut self) -> Pe11AfcfgW<PcfeSpec> {
        Pe11AfcfgW::new(self, 22)
    }
    #[doc = "Bit 24 - PE12 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pe12_afcfg(&mut self) -> Pe12AfcfgW<PcfeSpec> {
        Pe12AfcfgW::new(self, 24)
    }
    #[doc = "Bit 26 - PE13 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pe13_afcfg(&mut self) -> Pe13AfcfgW<PcfeSpec> {
        Pe13AfcfgW::new(self, 26)
    }
}
#[doc = "AFIO port configuration register E\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pcfe::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pcfe::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PcfeSpec;
impl crate::RegisterSpec for PcfeSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pcfe::R`](R) reader structure"]
impl crate::Readable for PcfeSpec {}
#[doc = "`write(|w| ..)` method takes [`pcfe::W`](W) writer structure"]
impl crate::Writable for PcfeSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PCFE to value 0"]
impl crate::Resettable for PcfeSpec {
    const RESET_VALUE: u32 = 0;
}
