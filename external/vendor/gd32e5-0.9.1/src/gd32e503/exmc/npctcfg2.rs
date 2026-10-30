#[doc = "Register `NPCTCFG2` reader"]
pub type R = crate::R<Npctcfg2Spec>;
#[doc = "Register `NPCTCFG2` writer"]
pub type W = crate::W<Npctcfg2Spec>;
#[doc = "Field `COMSET` reader - Common memory setup time"]
pub type ComsetR = crate::FieldReader;
#[doc = "Field `COMSET` writer - Common memory setup time"]
pub type ComsetW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `COMWAIT` reader - Common memory wait time"]
pub type ComwaitR = crate::FieldReader;
#[doc = "Field `COMWAIT` writer - Common memory wait time"]
pub type ComwaitW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `COMHLD` reader - Common memory hold time"]
pub type ComhldR = crate::FieldReader;
#[doc = "Field `COMHLD` writer - Common memory hold time"]
pub type ComhldW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `COMHIZ` reader - Common memory data bus HiZ time"]
pub type ComhizR = crate::FieldReader;
#[doc = "Field `COMHIZ` writer - Common memory data bus HiZ time"]
pub type ComhizW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - Common memory setup time"]
    #[inline(always)]
    pub fn comset(&self) -> ComsetR {
        ComsetR::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - Common memory wait time"]
    #[inline(always)]
    pub fn comwait(&self) -> ComwaitR {
        ComwaitR::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - Common memory hold time"]
    #[inline(always)]
    pub fn comhld(&self) -> ComhldR {
        ComhldR::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - Common memory data bus HiZ time"]
    #[inline(always)]
    pub fn comhiz(&self) -> ComhizR {
        ComhizR::new(((self.bits >> 24) & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:7 - Common memory setup time"]
    #[inline(always)]
    #[must_use]
    pub fn comset(&mut self) -> ComsetW<Npctcfg2Spec> {
        ComsetW::new(self, 0)
    }
    #[doc = "Bits 8:15 - Common memory wait time"]
    #[inline(always)]
    #[must_use]
    pub fn comwait(&mut self) -> ComwaitW<Npctcfg2Spec> {
        ComwaitW::new(self, 8)
    }
    #[doc = "Bits 16:23 - Common memory hold time"]
    #[inline(always)]
    #[must_use]
    pub fn comhld(&mut self) -> ComhldW<Npctcfg2Spec> {
        ComhldW::new(self, 16)
    }
    #[doc = "Bits 24:31 - Common memory data bus HiZ time"]
    #[inline(always)]
    #[must_use]
    pub fn comhiz(&mut self) -> ComhizW<Npctcfg2Spec> {
        ComhizW::new(self, 24)
    }
}
#[doc = "NAND flash/PC card common space timing configuration register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`npctcfg2::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`npctcfg2::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Npctcfg2Spec;
impl crate::RegisterSpec for Npctcfg2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`npctcfg2::R`](R) reader structure"]
impl crate::Readable for Npctcfg2Spec {}
#[doc = "`write(|w| ..)` method takes [`npctcfg2::W`](W) writer structure"]
impl crate::Writable for Npctcfg2Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets NPCTCFG2 to value 0xffff_ffff"]
impl crate::Resettable for Npctcfg2Spec {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
