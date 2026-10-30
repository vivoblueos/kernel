#[doc = "Register `HPCS` reader"]
pub type R = crate::R<HpcsSpec>;
#[doc = "Register `HPCS` writer"]
pub type W = crate::W<HpcsSpec>;
#[doc = "Field `PCST` reader - Port connect status"]
pub type PcstR = crate::BitReader;
#[doc = "Field `PCD` reader - Port connect detected"]
pub type PcdR = crate::BitReader;
#[doc = "Field `PCD` writer - Port connect detected"]
pub type PcdW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PE` reader - Port enable"]
pub type PeR = crate::BitReader;
#[doc = "Field `PE` writer - Port enable"]
pub type PeW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PEDC` reader - Port enable/disable change"]
pub type PedcR = crate::BitReader;
#[doc = "Field `PEDC` writer - Port enable/disable change"]
pub type PedcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PREM` reader - Port resume"]
pub type PremR = crate::BitReader;
#[doc = "Field `PREM` writer - Port resume"]
pub type PremW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PSP` reader - Port suspend"]
pub type PspR = crate::BitReader;
#[doc = "Field `PSP` writer - Port suspend"]
pub type PspW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PRST` reader - Port reset"]
pub type PrstR = crate::BitReader;
#[doc = "Field `PRST` writer - Port reset"]
pub type PrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PLST` reader - Port line status"]
pub type PlstR = crate::FieldReader;
#[doc = "Field `PP` reader - Port power"]
pub type PpR = crate::BitReader;
#[doc = "Field `PP` writer - Port power"]
pub type PpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PTEST` reader - Port Test control"]
pub type PtestR = crate::FieldReader;
#[doc = "Field `PTEST` writer - Port Test control"]
pub type PtestW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `PS` reader - Port speed"]
pub type PsR = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - Port connect status"]
    #[inline(always)]
    pub fn pcst(&self) -> PcstR {
        PcstR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Port connect detected"]
    #[inline(always)]
    pub fn pcd(&self) -> PcdR {
        PcdR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Port enable"]
    #[inline(always)]
    pub fn pe(&self) -> PeR {
        PeR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Port enable/disable change"]
    #[inline(always)]
    pub fn pedc(&self) -> PedcR {
        PedcR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 6 - Port resume"]
    #[inline(always)]
    pub fn prem(&self) -> PremR {
        PremR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Port suspend"]
    #[inline(always)]
    pub fn psp(&self) -> PspR {
        PspR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Port reset"]
    #[inline(always)]
    pub fn prst(&self) -> PrstR {
        PrstR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bits 10:11 - Port line status"]
    #[inline(always)]
    pub fn plst(&self) -> PlstR {
        PlstR::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bit 12 - Port power"]
    #[inline(always)]
    pub fn pp(&self) -> PpR {
        PpR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bits 13:16 - Port Test control"]
    #[inline(always)]
    pub fn ptest(&self) -> PtestR {
        PtestR::new(((self.bits >> 13) & 0x0f) as u8)
    }
    #[doc = "Bits 17:18 - Port speed"]
    #[inline(always)]
    pub fn ps(&self) -> PsR {
        PsR::new(((self.bits >> 17) & 3) as u8)
    }
}
impl W {
    #[doc = "Bit 1 - Port connect detected"]
    #[inline(always)]
    #[must_use]
    pub fn pcd(&mut self) -> PcdW<HpcsSpec> {
        PcdW::new(self, 1)
    }
    #[doc = "Bit 2 - Port enable"]
    #[inline(always)]
    #[must_use]
    pub fn pe(&mut self) -> PeW<HpcsSpec> {
        PeW::new(self, 2)
    }
    #[doc = "Bit 3 - Port enable/disable change"]
    #[inline(always)]
    #[must_use]
    pub fn pedc(&mut self) -> PedcW<HpcsSpec> {
        PedcW::new(self, 3)
    }
    #[doc = "Bit 6 - Port resume"]
    #[inline(always)]
    #[must_use]
    pub fn prem(&mut self) -> PremW<HpcsSpec> {
        PremW::new(self, 6)
    }
    #[doc = "Bit 7 - Port suspend"]
    #[inline(always)]
    #[must_use]
    pub fn psp(&mut self) -> PspW<HpcsSpec> {
        PspW::new(self, 7)
    }
    #[doc = "Bit 8 - Port reset"]
    #[inline(always)]
    #[must_use]
    pub fn prst(&mut self) -> PrstW<HpcsSpec> {
        PrstW::new(self, 8)
    }
    #[doc = "Bit 12 - Port power"]
    #[inline(always)]
    #[must_use]
    pub fn pp(&mut self) -> PpW<HpcsSpec> {
        PpW::new(self, 12)
    }
    #[doc = "Bits 13:16 - Port Test control"]
    #[inline(always)]
    #[must_use]
    pub fn ptest(&mut self) -> PtestW<HpcsSpec> {
        PtestW::new(self, 13)
    }
}
#[doc = "Host port control and status register (USBFS_HPCS)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hpcs::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hpcs::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HpcsSpec;
impl crate::RegisterSpec for HpcsSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hpcs::R`](R) reader structure"]
impl crate::Readable for HpcsSpec {}
#[doc = "`write(|w| ..)` method takes [`hpcs::W`](W) writer structure"]
impl crate::Writable for HpcsSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets HPCS to value 0"]
impl crate::Resettable for HpcsSpec {
    const RESET_VALUE: u32 = 0;
}
