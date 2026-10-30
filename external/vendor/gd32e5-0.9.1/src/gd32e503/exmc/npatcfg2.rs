#[doc = "Register `NPATCFG2` reader"]
pub type R = crate::R<Npatcfg2Spec>;
#[doc = "Register `NPATCFG2` writer"]
pub type W = crate::W<Npatcfg2Spec>;
#[doc = "Field `ATTSET` reader - Attribute memory setup time"]
pub type AttsetR = crate::FieldReader;
#[doc = "Field `ATTSET` writer - Attribute memory setup time"]
pub type AttsetW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `ATTWAIT` reader - Attribute memory wait time"]
pub type AttwaitR = crate::FieldReader;
#[doc = "Field `ATTWAIT` writer - Attribute memory wait time"]
pub type AttwaitW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `ATTHLD` reader - Attribute memory hold time"]
pub type AtthldR = crate::FieldReader;
#[doc = "Field `ATTHLD` writer - Attribute memory hold time"]
pub type AtthldW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `ATTHIZ` reader - Attribute memory data bus HiZ time"]
pub type AtthizR = crate::FieldReader;
#[doc = "Field `ATTHIZ` writer - Attribute memory data bus HiZ time"]
pub type AtthizW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - Attribute memory setup time"]
    #[inline(always)]
    pub fn attset(&self) -> AttsetR {
        AttsetR::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - Attribute memory wait time"]
    #[inline(always)]
    pub fn attwait(&self) -> AttwaitR {
        AttwaitR::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - Attribute memory hold time"]
    #[inline(always)]
    pub fn atthld(&self) -> AtthldR {
        AtthldR::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - Attribute memory data bus HiZ time"]
    #[inline(always)]
    pub fn atthiz(&self) -> AtthizR {
        AtthizR::new(((self.bits >> 24) & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:7 - Attribute memory setup time"]
    #[inline(always)]
    #[must_use]
    pub fn attset(&mut self) -> AttsetW<Npatcfg2Spec> {
        AttsetW::new(self, 0)
    }
    #[doc = "Bits 8:15 - Attribute memory wait time"]
    #[inline(always)]
    #[must_use]
    pub fn attwait(&mut self) -> AttwaitW<Npatcfg2Spec> {
        AttwaitW::new(self, 8)
    }
    #[doc = "Bits 16:23 - Attribute memory hold time"]
    #[inline(always)]
    #[must_use]
    pub fn atthld(&mut self) -> AtthldW<Npatcfg2Spec> {
        AtthldW::new(self, 16)
    }
    #[doc = "Bits 24:31 - Attribute memory data bus HiZ time"]
    #[inline(always)]
    #[must_use]
    pub fn atthiz(&mut self) -> AtthizW<Npatcfg2Spec> {
        AtthizW::new(self, 24)
    }
}
#[doc = "NAND flash/PC card attribute space timing configuration register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npatcfg2::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npatcfg2::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Npatcfg2Spec;
impl crate::RegisterSpec for Npatcfg2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`npatcfg2::R`](R) reader structure"]
impl crate::Readable for Npatcfg2Spec {}
#[doc = "`write(|w| ..)` method takes [`npatcfg2::W`](W) writer structure"]
impl crate::Writable for Npatcfg2Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets NPATCFG2 to value 0xffff_ffff"]
impl crate::Resettable for Npatcfg2Spec {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
