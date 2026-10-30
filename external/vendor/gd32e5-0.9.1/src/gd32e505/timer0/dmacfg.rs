#[doc = "Register `DMACFG` reader"]
pub type R = crate::R<DmacfgSpec>;
#[doc = "Register `DMACFG` writer"]
pub type W = crate::W<DmacfgSpec>;
#[doc = "Field `DMATA` reader - DMA transfer access start address"]
pub type DmataR = crate::FieldReader;
#[doc = "Field `DMATA` writer - DMA transfer access start address"]
pub type DmataW<'a, REG> = crate::FieldWriterSafe<'a, REG, 5>;
#[doc = "Field `DMATC` reader - DMA transfer count"]
pub type DmatcR = crate::FieldReader;
#[doc = "Field `DMATC` writer - DMA transfer count"]
pub type DmatcW<'a, REG> = crate::FieldWriterSafe<'a, REG, 5>;
impl R {
    #[doc = "Bits 0:4 - DMA transfer access start address"]
    #[inline(always)]
    pub fn dmata(&self) -> DmataR {
        DmataR::new((self.bits & 0x1f) as u8)
    }
    #[doc = "Bits 8:12 - DMA transfer count"]
    #[inline(always)]
    pub fn dmatc(&self) -> DmatcR {
        DmatcR::new(((self.bits >> 8) & 0x1f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:4 - DMA transfer access start address"]
    #[inline(always)]
    #[must_use]
    pub fn dmata(&mut self) -> DmataW<DmacfgSpec> {
        DmataW::new(self, 0)
    }
    #[doc = "Bits 8:12 - DMA transfer count"]
    #[inline(always)]
    #[must_use]
    pub fn dmatc(&mut self) -> DmatcW<DmacfgSpec> {
        DmatcW::new(self, 8)
    }
}
#[doc = "DMA configuration register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmacfg::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmacfg::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DmacfgSpec;
impl crate::RegisterSpec for DmacfgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dmacfg::R`](R) reader structure"]
impl crate::Readable for DmacfgSpec {}
#[doc = "`write(|w| ..)` method takes [`dmacfg::W`](W) writer structure"]
impl crate::Writable for DmacfgSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DMACFG to value 0"]
impl crate::Resettable for DmacfgSpec {
    const RESET_VALUE: u32 = 0;
}
