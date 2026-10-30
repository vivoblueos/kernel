#[doc = "Register `SNTCFG0` reader"]
pub type R = crate::R<Sntcfg0Spec>;
#[doc = "Register `SNTCFG0` writer"]
pub type W = crate::W<Sntcfg0Spec>;
#[doc = "Field `ASET` reader - Address setup time"]
pub type AsetR = crate::FieldReader;
#[doc = "Field `ASET` writer - Address setup time"]
pub type AsetW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `AHLD` reader - Address hold time"]
pub type AhldR = crate::FieldReader;
#[doc = "Field `AHLD` writer - Address hold time"]
pub type AhldW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `DSET` reader - Data setup time"]
pub type DsetR = crate::FieldReader;
#[doc = "Field `DSET` writer - Data setup time"]
pub type DsetW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `BUSLAT` reader - Bus latency"]
pub type BuslatR = crate::FieldReader;
#[doc = "Field `BUSLAT` writer - Bus latency"]
pub type BuslatW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CKDIV` reader - Synchronous clock divide ratio"]
pub type CkdivR = crate::FieldReader;
#[doc = "Field `CKDIV` writer - Synchronous clock divide ratio"]
pub type CkdivW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `DLAT` reader - Data latency for NOR Flash"]
pub type DlatR = crate::FieldReader;
#[doc = "Field `DLAT` writer - Data latency for NOR Flash"]
pub type DlatW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `ASYNCMOD` reader - Asynchronous access mode"]
pub type AsyncmodR = crate::FieldReader;
#[doc = "Field `ASYNCMOD` writer - Asynchronous access mode"]
pub type AsyncmodW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:3 - Address setup time"]
    #[inline(always)]
    pub fn aset(&self) -> AsetR {
        AsetR::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:7 - Address hold time"]
    #[inline(always)]
    pub fn ahld(&self) -> AhldR {
        AhldR::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bits 8:15 - Data setup time"]
    #[inline(always)]
    pub fn dset(&self) -> DsetR {
        DsetR::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:19 - Bus latency"]
    #[inline(always)]
    pub fn buslat(&self) -> BuslatR {
        BuslatR::new(((self.bits >> 16) & 0x0f) as u8)
    }
    #[doc = "Bits 20:23 - Synchronous clock divide ratio"]
    #[inline(always)]
    pub fn ckdiv(&self) -> CkdivR {
        CkdivR::new(((self.bits >> 20) & 0x0f) as u8)
    }
    #[doc = "Bits 24:27 - Data latency for NOR Flash"]
    #[inline(always)]
    pub fn dlat(&self) -> DlatR {
        DlatR::new(((self.bits >> 24) & 0x0f) as u8)
    }
    #[doc = "Bits 28:29 - Asynchronous access mode"]
    #[inline(always)]
    pub fn asyncmod(&self) -> AsyncmodR {
        AsyncmodR::new(((self.bits >> 28) & 3) as u8)
    }
}
impl W {
    #[doc = "Bits 0:3 - Address setup time"]
    #[inline(always)]
    #[must_use]
    pub fn aset(&mut self) -> AsetW<Sntcfg0Spec> {
        AsetW::new(self, 0)
    }
    #[doc = "Bits 4:7 - Address hold time"]
    #[inline(always)]
    #[must_use]
    pub fn ahld(&mut self) -> AhldW<Sntcfg0Spec> {
        AhldW::new(self, 4)
    }
    #[doc = "Bits 8:15 - Data setup time"]
    #[inline(always)]
    #[must_use]
    pub fn dset(&mut self) -> DsetW<Sntcfg0Spec> {
        DsetW::new(self, 8)
    }
    #[doc = "Bits 16:19 - Bus latency"]
    #[inline(always)]
    #[must_use]
    pub fn buslat(&mut self) -> BuslatW<Sntcfg0Spec> {
        BuslatW::new(self, 16)
    }
    #[doc = "Bits 20:23 - Synchronous clock divide ratio"]
    #[inline(always)]
    #[must_use]
    pub fn ckdiv(&mut self) -> CkdivW<Sntcfg0Spec> {
        CkdivW::new(self, 20)
    }
    #[doc = "Bits 24:27 - Data latency for NOR Flash"]
    #[inline(always)]
    #[must_use]
    pub fn dlat(&mut self) -> DlatW<Sntcfg0Spec> {
        DlatW::new(self, 24)
    }
    #[doc = "Bits 28:29 - Asynchronous access mode"]
    #[inline(always)]
    #[must_use]
    pub fn asyncmod(&mut self) -> AsyncmodW<Sntcfg0Spec> {
        AsyncmodW::new(self, 28)
    }
}
#[doc = "SRAM/NOR flash timing configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`sntcfg0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`sntcfg0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Sntcfg0Spec;
impl crate::RegisterSpec for Sntcfg0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sntcfg0::R`](R) reader structure"]
impl crate::Readable for Sntcfg0Spec {}
#[doc = "`write(|w| ..)` method takes [`sntcfg0::W`](W) writer structure"]
impl crate::Writable for Sntcfg0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets SNTCFG0 to value 0x0fff_ffff"]
impl crate::Resettable for Sntcfg0Spec {
    const RESET_VALUE: u32 = 0x0fff_ffff;
}
