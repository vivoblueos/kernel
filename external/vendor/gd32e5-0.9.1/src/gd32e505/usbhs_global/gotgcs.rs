#[doc = "Register `GOTGCS` reader"]
pub type R = crate::R<GotgcsSpec>;
#[doc = "Register `GOTGCS` writer"]
pub type W = crate::W<GotgcsSpec>;
#[doc = "Field `SRPS` reader - SRP success"]
pub type SrpsR = crate::BitReader;
#[doc = "Field `SRPREQ` reader - SRP request"]
pub type SrpreqR = crate::BitReader;
#[doc = "Field `SRPREQ` writer - SRP request"]
pub type SrpreqW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `VOE` reader - Override enable of VBUS valid"]
pub type VoeR = crate::BitReader;
#[doc = "Field `VOE` writer - Override enable of VBUS valid"]
pub type VoeW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `VOV` reader - Override value of VBUS valid"]
pub type VovR = crate::BitReader;
#[doc = "Field `VOV` writer - Override value of VBUS valid"]
pub type VovW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AVOE` reader - Override enable of A-peripheral session valid"]
pub type AvoeR = crate::BitReader;
#[doc = "Field `AVOE` writer - Override enable of A-peripheral session valid"]
pub type AvoeW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AVOV` reader - Override value of A-peripheral session valid"]
pub type AvovR = crate::BitReader;
#[doc = "Field `AVOV` writer - Override value of A-peripheral session valid"]
pub type AvovW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BVOE` reader - Override enable of B-peripheral session valid"]
pub type BvoeR = crate::BitReader;
#[doc = "Field `BVOE` writer - Override enable of B-peripheral session valid"]
pub type BvoeW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BVOV` reader - Override value of B-peripheral session valid"]
pub type BvovR = crate::BitReader;
#[doc = "Field `BVOV` writer - Override value of B-peripheral session valid"]
pub type BvovW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HNPS` reader - HNP success"]
pub type HnpsR = crate::BitReader;
#[doc = "Field `HNPREQ` reader - HNP request"]
pub type HnpreqR = crate::BitReader;
#[doc = "Field `HNPREQ` writer - HNP request"]
pub type HnpreqW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HHNPEN` reader - Host HNP enable"]
pub type HhnpenR = crate::BitReader;
#[doc = "Field `HHNPEN` writer - Host HNP enable"]
pub type HhnpenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DHNPEN` reader - Device HNP enabled"]
pub type DhnpenR = crate::BitReader;
#[doc = "Field `DHNPEN` writer - Device HNP enabled"]
pub type DhnpenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EHE` reader - Embedded host enable"]
pub type EheR = crate::BitReader;
#[doc = "Field `EHE` writer - Embedded host enable"]
pub type EheW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IDPS` reader - ID pin status"]
pub type IdpsR = crate::BitReader;
#[doc = "Field `DI` reader - Debounce interval"]
pub type DiR = crate::BitReader;
#[doc = "Field `ASV` reader - A-session valid"]
pub type AsvR = crate::BitReader;
#[doc = "Field `BSV` reader - B-session valid"]
pub type BsvR = crate::BitReader;
#[doc = "Field `OV` reader - Select OTG version"]
pub type OvR = crate::BitReader;
#[doc = "Field `OV` writer - Select OTG version"]
pub type OvW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - SRP success"]
    #[inline(always)]
    pub fn srps(&self) -> SrpsR {
        SrpsR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - SRP request"]
    #[inline(always)]
    pub fn srpreq(&self) -> SrpreqR {
        SrpreqR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Override enable of VBUS valid"]
    #[inline(always)]
    pub fn voe(&self) -> VoeR {
        VoeR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Override value of VBUS valid"]
    #[inline(always)]
    pub fn vov(&self) -> VovR {
        VovR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Override enable of A-peripheral session valid"]
    #[inline(always)]
    pub fn avoe(&self) -> AvoeR {
        AvoeR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Override value of A-peripheral session valid"]
    #[inline(always)]
    pub fn avov(&self) -> AvovR {
        AvovR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Override enable of B-peripheral session valid"]
    #[inline(always)]
    pub fn bvoe(&self) -> BvoeR {
        BvoeR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Override value of B-peripheral session valid"]
    #[inline(always)]
    pub fn bvov(&self) -> BvovR {
        BvovR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - HNP success"]
    #[inline(always)]
    pub fn hnps(&self) -> HnpsR {
        HnpsR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - HNP request"]
    #[inline(always)]
    pub fn hnpreq(&self) -> HnpreqR {
        HnpreqR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Host HNP enable"]
    #[inline(always)]
    pub fn hhnpen(&self) -> HhnpenR {
        HhnpenR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Device HNP enabled"]
    #[inline(always)]
    pub fn dhnpen(&self) -> DhnpenR {
        DhnpenR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Embedded host enable"]
    #[inline(always)]
    pub fn ehe(&self) -> EheR {
        EheR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 16 - ID pin status"]
    #[inline(always)]
    pub fn idps(&self) -> IdpsR {
        IdpsR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Debounce interval"]
    #[inline(always)]
    pub fn di(&self) -> DiR {
        DiR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - A-session valid"]
    #[inline(always)]
    pub fn asv(&self) -> AsvR {
        AsvR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - B-session valid"]
    #[inline(always)]
    pub fn bsv(&self) -> BsvR {
        BsvR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Select OTG version"]
    #[inline(always)]
    pub fn ov(&self) -> OvR {
        OvR::new(((self.bits >> 20) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 1 - SRP request"]
    #[inline(always)]
    #[must_use]
    pub fn srpreq(&mut self) -> SrpreqW<GotgcsSpec> {
        SrpreqW::new(self, 1)
    }
    #[doc = "Bit 2 - Override enable of VBUS valid"]
    #[inline(always)]
    #[must_use]
    pub fn voe(&mut self) -> VoeW<GotgcsSpec> {
        VoeW::new(self, 2)
    }
    #[doc = "Bit 3 - Override value of VBUS valid"]
    #[inline(always)]
    #[must_use]
    pub fn vov(&mut self) -> VovW<GotgcsSpec> {
        VovW::new(self, 3)
    }
    #[doc = "Bit 4 - Override enable of A-peripheral session valid"]
    #[inline(always)]
    #[must_use]
    pub fn avoe(&mut self) -> AvoeW<GotgcsSpec> {
        AvoeW::new(self, 4)
    }
    #[doc = "Bit 5 - Override value of A-peripheral session valid"]
    #[inline(always)]
    #[must_use]
    pub fn avov(&mut self) -> AvovW<GotgcsSpec> {
        AvovW::new(self, 5)
    }
    #[doc = "Bit 6 - Override enable of B-peripheral session valid"]
    #[inline(always)]
    #[must_use]
    pub fn bvoe(&mut self) -> BvoeW<GotgcsSpec> {
        BvoeW::new(self, 6)
    }
    #[doc = "Bit 7 - Override value of B-peripheral session valid"]
    #[inline(always)]
    #[must_use]
    pub fn bvov(&mut self) -> BvovW<GotgcsSpec> {
        BvovW::new(self, 7)
    }
    #[doc = "Bit 9 - HNP request"]
    #[inline(always)]
    #[must_use]
    pub fn hnpreq(&mut self) -> HnpreqW<GotgcsSpec> {
        HnpreqW::new(self, 9)
    }
    #[doc = "Bit 10 - Host HNP enable"]
    #[inline(always)]
    #[must_use]
    pub fn hhnpen(&mut self) -> HhnpenW<GotgcsSpec> {
        HhnpenW::new(self, 10)
    }
    #[doc = "Bit 11 - Device HNP enabled"]
    #[inline(always)]
    #[must_use]
    pub fn dhnpen(&mut self) -> DhnpenW<GotgcsSpec> {
        DhnpenW::new(self, 11)
    }
    #[doc = "Bit 12 - Embedded host enable"]
    #[inline(always)]
    #[must_use]
    pub fn ehe(&mut self) -> EheW<GotgcsSpec> {
        EheW::new(self, 12)
    }
    #[doc = "Bit 20 - Select OTG version"]
    #[inline(always)]
    #[must_use]
    pub fn ov(&mut self) -> OvW<GotgcsSpec> {
        OvW::new(self, 20)
    }
}
#[doc = "Global OTG control and status register (USBFS_GOTGCS)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`gotgcs::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`gotgcs::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GotgcsSpec;
impl crate::RegisterSpec for GotgcsSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`gotgcs::R`](R) reader structure"]
impl crate::Readable for GotgcsSpec {}
#[doc = "`write(|w| ..)` method takes [`gotgcs::W`](W) writer structure"]
impl crate::Writable for GotgcsSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets GOTGCS to value 0x0800"]
impl crate::Resettable for GotgcsSpec {
    const RESET_VALUE: u32 = 0x0800;
}
