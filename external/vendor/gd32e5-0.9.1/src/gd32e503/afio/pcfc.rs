#[doc = "Register `PCFC` reader"]
pub type R = crate::R<PcfcSpec>;
#[doc = "Register `PCFC` writer"]
pub type W = crate::W<PcfcSpec>;
#[doc = "Field `PC0_AFCFG` reader - PC0 AF function configuration bitse"]
pub type Pc0AfcfgR = crate::BitReader;
#[doc = "Field `PC0_AFCFG` writer - PC0 AF function configuration bitse"]
pub type Pc0AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PC2_AFCFG` reader - PC2 AF function configuration bitse"]
pub type Pc2AfcfgR = crate::FieldReader;
#[doc = "Field `PC2_AFCFG` writer - PC2 AF function configuration bitse"]
pub type Pc2AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PC3_AFCFG` reader - PC3 AF function configuration bitse"]
pub type Pc3AfcfgR = crate::BitReader;
#[doc = "Field `PC3_AFCFG` writer - PC3 AF function configuration bitse"]
pub type Pc3AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PC6_AFCFG` reader - PC6 AF function configuration bitse"]
pub type Pc6AfcfgR = crate::FieldReader;
#[doc = "Field `PC6_AFCFG` writer - PC6 AF function configuration bitse"]
pub type Pc6AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PC7_AFCFG` reader - PC7 AF function configuration bitse"]
pub type Pc7AfcfgR = crate::FieldReader;
#[doc = "Field `PC7_AFCFG` writer - PC7 AF function configuration bitse"]
pub type Pc7AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PC8_AFCFG` reader - PC8 AF function configuration bitse"]
pub type Pc8AfcfgR = crate::FieldReader;
#[doc = "Field `PC8_AFCFG` writer - PC8 AF function configuration bitse"]
pub type Pc8AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PC9_AFCFG` reader - PC9 AF function configuration bitse"]
pub type Pc9AfcfgR = crate::FieldReader;
#[doc = "Field `PC9_AFCFG` writer - PC9 AF function configuration bitse"]
pub type Pc9AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PC10_AFCFG` reader - PC10 AF function configuration bitse"]
pub type Pc10AfcfgR = crate::BitReader;
#[doc = "Field `PC10_AFCFG` writer - PC10 AF function configuration bitse"]
pub type Pc10AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PC11_AFCFG` reader - PC11 AF function configuration bitse"]
pub type Pc11AfcfgR = crate::FieldReader;
#[doc = "Field `PC11_AFCFG` writer - PC11 AF function configuration bitse"]
pub type Pc11AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PC12_AFCFG` reader - PC12 AF function configuration bitse"]
pub type Pc12AfcfgR = crate::BitReader;
#[doc = "Field `PC12_AFCFG` writer - PC12 AF function configuration bitse"]
pub type Pc12AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - PC0 AF function configuration bitse"]
    #[inline(always)]
    pub fn pc0_afcfg(&self) -> Pc0AfcfgR {
        Pc0AfcfgR::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 4:5 - PC2 AF function configuration bitse"]
    #[inline(always)]
    pub fn pc2_afcfg(&self) -> Pc2AfcfgR {
        Pc2AfcfgR::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bit 6 - PC3 AF function configuration bitse"]
    #[inline(always)]
    pub fn pc3_afcfg(&self) -> Pc3AfcfgR {
        Pc3AfcfgR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bits 12:13 - PC6 AF function configuration bitse"]
    #[inline(always)]
    pub fn pc6_afcfg(&self) -> Pc6AfcfgR {
        Pc6AfcfgR::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bits 14:15 - PC7 AF function configuration bitse"]
    #[inline(always)]
    pub fn pc7_afcfg(&self) -> Pc7AfcfgR {
        Pc7AfcfgR::new(((self.bits >> 14) & 3) as u8)
    }
    #[doc = "Bits 16:17 - PC8 AF function configuration bitse"]
    #[inline(always)]
    pub fn pc8_afcfg(&self) -> Pc8AfcfgR {
        Pc8AfcfgR::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 18:19 - PC9 AF function configuration bitse"]
    #[inline(always)]
    pub fn pc9_afcfg(&self) -> Pc9AfcfgR {
        Pc9AfcfgR::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bit 20 - PC10 AF function configuration bitse"]
    #[inline(always)]
    pub fn pc10_afcfg(&self) -> Pc10AfcfgR {
        Pc10AfcfgR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bits 22:23 - PC11 AF function configuration bitse"]
    #[inline(always)]
    pub fn pc11_afcfg(&self) -> Pc11AfcfgR {
        Pc11AfcfgR::new(((self.bits >> 22) & 3) as u8)
    }
    #[doc = "Bit 24 - PC12 AF function configuration bitse"]
    #[inline(always)]
    pub fn pc12_afcfg(&self) -> Pc12AfcfgR {
        Pc12AfcfgR::new(((self.bits >> 24) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - PC0 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pc0_afcfg(&mut self) -> Pc0AfcfgW<PcfcSpec> {
        Pc0AfcfgW::new(self, 0)
    }
    #[doc = "Bits 4:5 - PC2 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pc2_afcfg(&mut self) -> Pc2AfcfgW<PcfcSpec> {
        Pc2AfcfgW::new(self, 4)
    }
    #[doc = "Bit 6 - PC3 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pc3_afcfg(&mut self) -> Pc3AfcfgW<PcfcSpec> {
        Pc3AfcfgW::new(self, 6)
    }
    #[doc = "Bits 12:13 - PC6 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pc6_afcfg(&mut self) -> Pc6AfcfgW<PcfcSpec> {
        Pc6AfcfgW::new(self, 12)
    }
    #[doc = "Bits 14:15 - PC7 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pc7_afcfg(&mut self) -> Pc7AfcfgW<PcfcSpec> {
        Pc7AfcfgW::new(self, 14)
    }
    #[doc = "Bits 16:17 - PC8 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pc8_afcfg(&mut self) -> Pc8AfcfgW<PcfcSpec> {
        Pc8AfcfgW::new(self, 16)
    }
    #[doc = "Bits 18:19 - PC9 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pc9_afcfg(&mut self) -> Pc9AfcfgW<PcfcSpec> {
        Pc9AfcfgW::new(self, 18)
    }
    #[doc = "Bit 20 - PC10 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pc10_afcfg(&mut self) -> Pc10AfcfgW<PcfcSpec> {
        Pc10AfcfgW::new(self, 20)
    }
    #[doc = "Bits 22:23 - PC11 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pc11_afcfg(&mut self) -> Pc11AfcfgW<PcfcSpec> {
        Pc11AfcfgW::new(self, 22)
    }
    #[doc = "Bit 24 - PC12 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pc12_afcfg(&mut self) -> Pc12AfcfgW<PcfcSpec> {
        Pc12AfcfgW::new(self, 24)
    }
}
#[doc = "AFIO port configuration register C\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pcfc::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pcfc::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PcfcSpec;
impl crate::RegisterSpec for PcfcSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pcfc::R`](R) reader structure"]
impl crate::Readable for PcfcSpec {}
#[doc = "`write(|w| ..)` method takes [`pcfc::W`](W) writer structure"]
impl crate::Writable for PcfcSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PCFC to value 0"]
impl crate::Resettable for PcfcSpec {
    const RESET_VALUE: u32 = 0;
}
