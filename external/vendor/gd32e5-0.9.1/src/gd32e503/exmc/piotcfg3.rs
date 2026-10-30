#[doc = "Register `PIOTCFG3` reader"]
pub type R = crate::R<Piotcfg3Spec>;
#[doc = "Register `PIOTCFG3` writer"]
pub type W = crate::W<Piotcfg3Spec>;
#[doc = "Field `IOSET` reader - IO space setup time"]
pub type IosetR = crate::FieldReader;
#[doc = "Field `IOSET` writer - IO space setup time"]
pub type IosetW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `IOWAIT` reader - IO space wait time"]
pub type IowaitR = crate::FieldReader;
#[doc = "Field `IOWAIT` writer - IO space wait time"]
pub type IowaitW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `IOHLD` reader - IO space hold time"]
pub type IohldR = crate::FieldReader;
#[doc = "Field `IOHLD` writer - IO space hold time"]
pub type IohldW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `IOHIZ` reader - IO space data bus HiZ time"]
pub type IohizR = crate::FieldReader;
#[doc = "Field `IOHIZ` writer - IO space data bus HiZ time"]
pub type IohizW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - IO space setup time"]
    #[inline(always)]
    pub fn ioset(&self) -> IosetR {
        IosetR::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - IO space wait time"]
    #[inline(always)]
    pub fn iowait(&self) -> IowaitR {
        IowaitR::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - IO space hold time"]
    #[inline(always)]
    pub fn iohld(&self) -> IohldR {
        IohldR::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - IO space data bus HiZ time"]
    #[inline(always)]
    pub fn iohiz(&self) -> IohizR {
        IohizR::new(((self.bits >> 24) & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:7 - IO space setup time"]
    #[inline(always)]
    #[must_use]
    pub fn ioset(&mut self) -> IosetW<Piotcfg3Spec> {
        IosetW::new(self, 0)
    }
    #[doc = "Bits 8:15 - IO space wait time"]
    #[inline(always)]
    #[must_use]
    pub fn iowait(&mut self) -> IowaitW<Piotcfg3Spec> {
        IowaitW::new(self, 8)
    }
    #[doc = "Bits 16:23 - IO space hold time"]
    #[inline(always)]
    #[must_use]
    pub fn iohld(&mut self) -> IohldW<Piotcfg3Spec> {
        IohldW::new(self, 16)
    }
    #[doc = "Bits 24:31 - IO space data bus HiZ time"]
    #[inline(always)]
    #[must_use]
    pub fn iohiz(&mut self) -> IohizW<Piotcfg3Spec> {
        IohizW::new(self, 24)
    }
}
#[doc = "PC card I/O space timing configuration register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`piotcfg3::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`piotcfg3::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Piotcfg3Spec;
impl crate::RegisterSpec for Piotcfg3Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`piotcfg3::R`](R) reader structure"]
impl crate::Readable for Piotcfg3Spec {}
#[doc = "`write(|w| ..)` method takes [`piotcfg3::W`](W) writer structure"]
impl crate::Writable for Piotcfg3Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PIOTCFG3 to value 0xffff_ffff"]
impl crate::Resettable for Piotcfg3Spec {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
