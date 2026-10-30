#[doc = "Register `PCFG` reader"]
pub type R = crate::R<PcfgSpec>;
#[doc = "Register `PCFG` writer"]
pub type W = crate::W<PcfgSpec>;
#[doc = "Field `PG6_AFCFG` reader - PG6 AF function configuration bitse"]
pub type Pg6AfcfgR = crate::BitReader;
#[doc = "Field `PG6_AFCFG` writer - PG6 AF function configuration bitse"]
pub type Pg6AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PG7_AFCFG` reader - PG7 AF function configuration bitse"]
pub type Pg7AfcfgR = crate::FieldReader;
#[doc = "Field `PG7_AFCFG` writer - PG7 AF function configuration bitse"]
pub type Pg7AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PG9_AFCFG` reader - PG9 AF function configuration bitse"]
pub type Pg9AfcfgR = crate::FieldReader;
#[doc = "Field `PG9_AFCFG` writer - PG9 AF function configuration bitse"]
pub type Pg9AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PG10_AFCFG` reader - PG10 AF function configuration bitse"]
pub type Pg10AfcfgR = crate::BitReader;
#[doc = "Field `PG10_AFCFG` writer - PG10 AF function configuration bitse"]
pub type Pg10AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PG11_AFCFG` reader - PG11 AF function configuration bitse"]
pub type Pg11AfcfgR = crate::FieldReader;
#[doc = "Field `PG11_AFCFG` writer - PG11 AF function configuration bitse"]
pub type Pg11AfcfgW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PG12_AFCFG` reader - PG12 AF function configuration bitse"]
pub type Pg12AfcfgR = crate::BitReader;
#[doc = "Field `PG12_AFCFG` writer - PG12 AF function configuration bitse"]
pub type Pg12AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PG13_AFCFG` reader - PG13 AF function configuration bitse"]
pub type Pg13AfcfgR = crate::BitReader;
#[doc = "Field `PG13_AFCFG` writer - PG13 AF function configuration bitse"]
pub type Pg13AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PG14_AFCFG` reader - PG14 AF function configuration bitse"]
pub type Pg14AfcfgR = crate::BitReader;
#[doc = "Field `PG14_AFCFG` writer - PG14 AF function configuration bitse"]
pub type Pg14AfcfgW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 12 - PG6 AF function configuration bitse"]
    #[inline(always)]
    pub fn pg6_afcfg(&self) -> Pg6AfcfgR {
        Pg6AfcfgR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bits 14:15 - PG7 AF function configuration bitse"]
    #[inline(always)]
    pub fn pg7_afcfg(&self) -> Pg7AfcfgR {
        Pg7AfcfgR::new(((self.bits >> 14) & 3) as u8)
    }
    #[doc = "Bits 18:19 - PG9 AF function configuration bitse"]
    #[inline(always)]
    pub fn pg9_afcfg(&self) -> Pg9AfcfgR {
        Pg9AfcfgR::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bit 20 - PG10 AF function configuration bitse"]
    #[inline(always)]
    pub fn pg10_afcfg(&self) -> Pg10AfcfgR {
        Pg10AfcfgR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bits 22:23 - PG11 AF function configuration bitse"]
    #[inline(always)]
    pub fn pg11_afcfg(&self) -> Pg11AfcfgR {
        Pg11AfcfgR::new(((self.bits >> 22) & 3) as u8)
    }
    #[doc = "Bit 24 - PG12 AF function configuration bitse"]
    #[inline(always)]
    pub fn pg12_afcfg(&self) -> Pg12AfcfgR {
        Pg12AfcfgR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 26 - PG13 AF function configuration bitse"]
    #[inline(always)]
    pub fn pg13_afcfg(&self) -> Pg13AfcfgR {
        Pg13AfcfgR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 28 - PG14 AF function configuration bitse"]
    #[inline(always)]
    pub fn pg14_afcfg(&self) -> Pg14AfcfgR {
        Pg14AfcfgR::new(((self.bits >> 28) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 12 - PG6 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pg6_afcfg(&mut self) -> Pg6AfcfgW<PcfgSpec> {
        Pg6AfcfgW::new(self, 12)
    }
    #[doc = "Bits 14:15 - PG7 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pg7_afcfg(&mut self) -> Pg7AfcfgW<PcfgSpec> {
        Pg7AfcfgW::new(self, 14)
    }
    #[doc = "Bits 18:19 - PG9 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pg9_afcfg(&mut self) -> Pg9AfcfgW<PcfgSpec> {
        Pg9AfcfgW::new(self, 18)
    }
    #[doc = "Bit 20 - PG10 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pg10_afcfg(&mut self) -> Pg10AfcfgW<PcfgSpec> {
        Pg10AfcfgW::new(self, 20)
    }
    #[doc = "Bits 22:23 - PG11 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pg11_afcfg(&mut self) -> Pg11AfcfgW<PcfgSpec> {
        Pg11AfcfgW::new(self, 22)
    }
    #[doc = "Bit 24 - PG12 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pg12_afcfg(&mut self) -> Pg12AfcfgW<PcfgSpec> {
        Pg12AfcfgW::new(self, 24)
    }
    #[doc = "Bit 26 - PG13 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pg13_afcfg(&mut self) -> Pg13AfcfgW<PcfgSpec> {
        Pg13AfcfgW::new(self, 26)
    }
    #[doc = "Bit 28 - PG14 AF function configuration bitse"]
    #[inline(always)]
    #[must_use]
    pub fn pg14_afcfg(&mut self) -> Pg14AfcfgW<PcfgSpec> {
        Pg14AfcfgW::new(self, 28)
    }
}
#[doc = "AFIO port configuration register G\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pcfg::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pcfg::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PcfgSpec;
impl crate::RegisterSpec for PcfgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pcfg::R`](R) reader structure"]
impl crate::Readable for PcfgSpec {}
#[doc = "`write(|w| ..)` method takes [`pcfg::W`](W) writer structure"]
impl crate::Writable for PcfgSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PCFG to value 0"]
impl crate::Resettable for PcfgSpec {
    const RESET_VALUE: u32 = 0;
}
