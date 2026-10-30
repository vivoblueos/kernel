#[doc = "Register `PCFB` reader"]
pub type R = crate::R<PcfbSpec>;
#[doc = "Register `PCFB` writer"]
pub type W = crate::W<PcfbSpec>;
#[doc = "Field `PB0_AFCFG` reader - PB0 AF function configuration bitse"]
pub type Pb0AfcfgR = crate::BitReader;
#[doc = "Field `PB0_AFCFG` writer - PB0 AF function configuration bitse"]
pub type Pb0AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PB1_AFCFG` reader - PB1 AF function configuration bitse"]
pub type Pb1AfcfgR = crate::FieldReader;
#[doc = "Field `PB1_AFCFG` writer - PB1 AF function configuration bitse"]
pub type Pb1AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PB2_AFCFG` reader - PB2 AF function configuration bitse"]
pub type Pb2AfcfgR = crate::FieldReader;
#[doc = "Field `PB2_AFCFG` writer - PB2 AF function configuration bitse"]
pub type Pb2AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PB3_AFCFG` reader - PB3 AF function configuration bitse"]
pub type Pb3AfcfgR = crate::BitReader;
#[doc = "Field `PB3_AFCFG` writer - PB3 AF function configuration bitse"]
pub type Pb3AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PB4_AFCFG` reader - PB4 AF function configuration bitse"]
pub type Pb4AfcfgR = crate::FieldReader;
#[doc = "Field `PB4_AFCFG` writer - PB4 AF function configuration bitse"]
pub type Pb4AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PB5_AFCFG` reader - PB5 AF function configuration bitse"]
pub type Pb5AfcfgR = crate::FieldReader;
#[doc = "Field `PB5_AFCFG` writer - PB5 AF function configuration bitse"]
pub type Pb5AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PB6_AFCFG` reader - PB6 AF function configuration bitse"]
pub type Pb6AfcfgR = crate::BitReader;
#[doc = "Field `PB6_AFCFG` writer - PB6 AF function configuration bitse"]
pub type Pb6AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PB7_AFCFG` reader - PB7 AF function configuration bitse"]
pub type Pb7AfcfgR = crate::BitReader;
#[doc = "Field `PB7_AFCFG` writer - PB7 AF function configuration bitse"]
pub type Pb7AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PB8_AFCFG` reader - PB8 AF function configuration bitse"]
pub type Pb8AfcfgR = crate::FieldReader;
#[doc = "Field `PB8_AFCFG` writer - PB8 AF function configuration bitse"]
pub type Pb8AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PB9_AFCFG` reader - PB9 AF function configuration bitse"]
pub type Pb9AfcfgR = crate::FieldReader;
#[doc = "Field `PB9_AFCFG` writer - PB9 AF function configuration bitse"]
pub type Pb9AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PB10_AFCFG` reader - PB10 AF function configuration bitse"]
pub type Pb10AfcfgR = crate::FieldReader;
#[doc = "Field `PB10_AFCFG` writer - PB10 AF function configuration bitse"]
pub type Pb10AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PB11_AFCFG` reader - PB11 AF function configuration bitse"]
pub type Pb11AfcfgR = crate::FieldReader;
#[doc = "Field `PB11_AFCFG` writer - PB11 AF function configuration bitse"]
pub type Pb11AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PB12_AFCFG` reader - PB12 AF function configuration bitse"]
pub type Pb12AfcfgR = crate::FieldReader;
#[doc = "Field `PB12_AFCFG` writer - PB12 AF function configuration bitse"]
pub type Pb12AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PB13_AFCFG` reader - PB13 AF function configuration bit"]
pub type Pb13AfcfgR = crate::FieldReader;
#[doc = "Field `PB13_AFCFG` writer - PB13 AF function configuration bit"]
pub type Pb13AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PB14_AFCFG` reader - PB14 AF function configuration bit"]
pub type Pb14AfcfgR = crate::FieldReader;
#[doc = "Field `PB14_AFCFG` writer - PB14 AF function configuration bit"]
pub type Pb14AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PB15_AFCFG` reader - PB15 AF function configuration bit"]
pub type Pb15AfcfgR = crate::BitReader;
#[doc = "Field `PB15_AFCFG` writer - PB15 AF function configuration bit"]
pub type Pb15AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - PB0 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb0_afcfg(&self) -> Pb0AfcfgR {
        Pb0AfcfgR::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 2:3 - PB1 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb1_afcfg(&self) -> Pb1AfcfgR {
        Pb1AfcfgR::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:5 - PB2 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb2_afcfg(&self) -> Pb2AfcfgR {
        Pb2AfcfgR::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bit 6 - PB3 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb3_afcfg(&self) -> Pb3AfcfgR {
        Pb3AfcfgR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bits 8:9 - PB4 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb4_afcfg(&self) -> Pb4AfcfgR {
        Pb4AfcfgR::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bits 10:11 - PB5 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb5_afcfg(&self) -> Pb5AfcfgR {
        Pb5AfcfgR::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bit 12 - PB6 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb6_afcfg(&self) -> Pb6AfcfgR {
        Pb6AfcfgR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 14 - PB7 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb7_afcfg(&self) -> Pb7AfcfgR {
        Pb7AfcfgR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bits 16:17 - PB8 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb8_afcfg(&self) -> Pb8AfcfgR {
        Pb8AfcfgR::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 18:19 - PB9 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb9_afcfg(&self) -> Pb9AfcfgR {
        Pb9AfcfgR::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bits 20:21 - PB10 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb10_afcfg(&self) -> Pb10AfcfgR {
        Pb10AfcfgR::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bits 22:23 - PB11 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb11_afcfg(&self) -> Pb11AfcfgR {
        Pb11AfcfgR::new(((self.bits >> 22) & 3) as u8)
    }
    #[doc = "Bits 24:25 - PB12 AF function configuration bitse"]
    #[inline(always)]
    pub fn pb12_afcfg(&self) -> Pb12AfcfgR {
        Pb12AfcfgR::new(((self.bits >> 24) & 3) as u8)
    }
    #[doc = "Bits 26:27 - PB13 AF function configuration bit"]
    #[inline(always)]
    pub fn pb13_afcfg(&self) -> Pb13AfcfgR {
        Pb13AfcfgR::new(((self.bits >> 26) & 3) as u8)
    }
    #[doc = "Bits 28:29 - PB14 AF function configuration bit"]
    #[inline(always)]
    pub fn pb14_afcfg(&self) -> Pb14AfcfgR {
        Pb14AfcfgR::new(((self.bits >> 28) & 3) as u8)
    }
    #[doc = "Bit 30 - PB15 AF function configuration bit"]
    #[inline(always)]
    pub fn pb15_afcfg(&self) -> Pb15AfcfgR {
        Pb15AfcfgR::new(((self.bits >> 30) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - PB0 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb0_afcfg(&mut self) -> Pb0AfcfgW<PcfbSpec> {
        Pb0AfcfgW::new(self, 0)
    }
    #[doc = "Bits 2:3 - PB1 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb1_afcfg(&mut self) -> Pb1AfcfgW<PcfbSpec> {
        Pb1AfcfgW::new(self, 2)
    }
    #[doc = "Bits 4:5 - PB2 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb2_afcfg(&mut self) -> Pb2AfcfgW<PcfbSpec> {
        Pb2AfcfgW::new(self, 4)
    }
    #[doc = "Bit 6 - PB3 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb3_afcfg(&mut self) -> Pb3AfcfgW<PcfbSpec> {
        Pb3AfcfgW::new(self, 6)
    }
    #[doc = "Bits 8:9 - PB4 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb4_afcfg(&mut self) -> Pb4AfcfgW<PcfbSpec> {
        Pb4AfcfgW::new(self, 8)
    }
    #[doc = "Bits 10:11 - PB5 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb5_afcfg(&mut self) -> Pb5AfcfgW<PcfbSpec> {
        Pb5AfcfgW::new(self, 10)
    }
    #[doc = "Bit 12 - PB6 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb6_afcfg(&mut self) -> Pb6AfcfgW<PcfbSpec> {
        Pb6AfcfgW::new(self, 12)
    }
    #[doc = "Bit 14 - PB7 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb7_afcfg(&mut self) -> Pb7AfcfgW<PcfbSpec> {
        Pb7AfcfgW::new(self, 14)
    }
    #[doc = "Bits 16:17 - PB8 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb8_afcfg(&mut self) -> Pb8AfcfgW<PcfbSpec> {
        Pb8AfcfgW::new(self, 16)
    }
    #[doc = "Bits 18:19 - PB9 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb9_afcfg(&mut self) -> Pb9AfcfgW<PcfbSpec> {
        Pb9AfcfgW::new(self, 18)
    }
    #[doc = "Bits 20:21 - PB10 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb10_afcfg(&mut self) -> Pb10AfcfgW<PcfbSpec> {
        Pb10AfcfgW::new(self, 20)
    }
    #[doc = "Bits 22:23 - PB11 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb11_afcfg(&mut self) -> Pb11AfcfgW<PcfbSpec> {
        Pb11AfcfgW::new(self, 22)
    }
    #[doc = "Bits 24:25 - PB12 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pb12_afcfg(&mut self) -> Pb12AfcfgW<PcfbSpec> {
        Pb12AfcfgW::new(self, 24)
    }
    #[doc = "Bits 26:27 - PB13 AF function configuration bit"]
    #[inline(always)]
    #[must_use]
    pub fn pb13_afcfg(&mut self) -> Pb13AfcfgW<PcfbSpec> {
        Pb13AfcfgW::new(self, 26)
    }
    #[doc = "Bits 28:29 - PB14 AF function configuration bit"]
    #[inline(always)]
    #[must_use]
    pub fn pb14_afcfg(&mut self) -> Pb14AfcfgW<PcfbSpec> {
        Pb14AfcfgW::new(self, 28)
    }
    #[doc = "Bit 30 - PB15 AF function configuration bit"]
    #[inline(always)]
    #[must_use]
    pub fn pb15_afcfg(&mut self) -> Pb15AfcfgW<PcfbSpec> {
        Pb15AfcfgW::new(self, 30)
    }
}
#[doc = "AFIO port configuration register B\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pcfb::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pcfb::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PcfbSpec;
impl crate::RegisterSpec for PcfbSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pcfb::R`](R) reader structure"]
impl crate::Readable for PcfbSpec {}
#[doc = "`write(|w| ..)` method takes [`pcfb::W`](W) writer structure"]
impl crate::Writable for PcfbSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PCFB to value 0"]
impl crate::Resettable for PcfbSpec {
    const RESET_VALUE: u32 = 0;
}
