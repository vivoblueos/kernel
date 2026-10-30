#[doc = "Register `ADPCTL` reader"]
pub type R = crate::R<AdpctlSpec>;
#[doc = "Register `ADPCTL` writer"]
pub type W = crate::W<AdpctlSpec>;
#[doc = "Field `DSCHGPR` reader - Time of probe discharge"]
pub type DschgprR = crate::FieldReader;
#[doc = "Field `DSCHGPR` writer - Time of probe discharge"]
pub type DschgprW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `RESOPR` reader - The resolution of CHGT value"]
pub type ResoprR = crate::FieldReader;
#[doc = "Field `RESOPR` writer - The resolution of CHGT value"]
pub type ResoprW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `PERPR` reader - Period of probe"]
pub type PerprR = crate::FieldReader;
#[doc = "Field `PERPR` writer - Period of probe"]
pub type PerprW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CHGT` reader - The latest time that VBUS ramps from VADPSINK to VADPPRB"]
pub type ChgtR = crate::FieldReader<u16>;
#[doc = "Field `PREN` reader - ADP probe enable"]
pub type PrenR = crate::BitReader;
#[doc = "Field `PREN` writer - ADP probe enable"]
pub type PrenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SNEN` reader - ADP sense enable"]
pub type SnenR = crate::BitReader;
#[doc = "Field `SNEN` writer - ADP sense enable"]
pub type SnenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADPRST` reader - ADP reset"]
pub type AdprstR = crate::BitReader;
#[doc = "Field `ADPEN` reader - ADP enable"]
pub type AdpenR = crate::BitReader;
#[doc = "Field `ADPEN` writer - ADP enable"]
pub type AdpenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADPPRF` reader - ADP probe interrupt flag"]
pub type AdpprfR = crate::BitReader;
#[doc = "Field `ADPPRF` writer - ADP probe interrupt flag"]
pub type AdpprfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADPSNF` reader - ADP sense interrupt flag"]
pub type AdpsnfR = crate::BitReader;
#[doc = "Field `ADPSNF` writer - ADP sense interrupt flag"]
pub type AdpsnfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADPTF` reader - ADP timeout interrupt flag"]
pub type AdptfR = crate::BitReader;
#[doc = "Field `ADPTF` writer - ADP timeout interrupt flag"]
pub type AdptfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADPPRFM` reader - The mask of ADP probe interrupt flag"]
pub type AdpprfmR = crate::BitReader;
#[doc = "Field `ADPPRFM` writer - The mask of ADP probe interrupt flag"]
pub type AdpprfmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADPSNFM` reader - The mask of ADP sense interrupt flag"]
pub type AdpsnfmR = crate::BitReader;
#[doc = "Field `ADPSNFM` writer - The mask of ADP sense interrupt flag"]
pub type AdpsnfmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADPTFM` reader - The mask of ADP timeout interrupt flag"]
pub type AdptfmR = crate::BitReader;
#[doc = "Field `ADPTFM` writer - The mask of ADP timeout interrupt flag"]
pub type AdptfmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RWR` reader - Read and write request"]
pub type RwrR = crate::FieldReader;
#[doc = "Field `RWR` writer - Read and write request"]
pub type RwrW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - Time of probe discharge"]
    #[inline(always)]
    pub fn dschgpr(&self) -> DschgprR {
        DschgprR::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:3 - The resolution of CHGT value"]
    #[inline(always)]
    pub fn resopr(&self) -> ResoprR {
        ResoprR::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:5 - Period of probe"]
    #[inline(always)]
    pub fn perpr(&self) -> PerprR {
        PerprR::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bits 6:16 - The latest time that VBUS ramps from VADPSINK to VADPPRB"]
    #[inline(always)]
    pub fn chgt(&self) -> ChgtR {
        ChgtR::new(((self.bits >> 6) & 0x07ff) as u16)
    }
    #[doc = "Bit 17 - ADP probe enable"]
    #[inline(always)]
    pub fn pren(&self) -> PrenR {
        PrenR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - ADP sense enable"]
    #[inline(always)]
    pub fn snen(&self) -> SnenR {
        SnenR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - ADP reset"]
    #[inline(always)]
    pub fn adprst(&self) -> AdprstR {
        AdprstR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - ADP enable"]
    #[inline(always)]
    pub fn adpen(&self) -> AdpenR {
        AdpenR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - ADP probe interrupt flag"]
    #[inline(always)]
    pub fn adpprf(&self) -> AdpprfR {
        AdpprfR::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - ADP sense interrupt flag"]
    #[inline(always)]
    pub fn adpsnf(&self) -> AdpsnfR {
        AdpsnfR::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - ADP timeout interrupt flag"]
    #[inline(always)]
    pub fn adptf(&self) -> AdptfR {
        AdptfR::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - The mask of ADP probe interrupt flag"]
    #[inline(always)]
    pub fn adpprfm(&self) -> AdpprfmR {
        AdpprfmR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - The mask of ADP sense interrupt flag"]
    #[inline(always)]
    pub fn adpsnfm(&self) -> AdpsnfmR {
        AdpsnfmR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - The mask of ADP timeout interrupt flag"]
    #[inline(always)]
    pub fn adptfm(&self) -> AdptfmR {
        AdptfmR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bits 27:28 - Read and write request"]
    #[inline(always)]
    pub fn rwr(&self) -> RwrR {
        RwrR::new(((self.bits >> 27) & 3) as u8)
    }
}
impl W {
    #[doc = "Bits 0:1 - Time of probe discharge"]
    #[inline(always)]
    #[must_use]
    pub fn dschgpr(&mut self) -> DschgprW<AdpctlSpec> {
        DschgprW::new(self, 0)
    }
    #[doc = "Bits 2:3 - The resolution of CHGT value"]
    #[inline(always)]
    #[must_use]
    pub fn resopr(&mut self) -> ResoprW<AdpctlSpec> {
        ResoprW::new(self, 2)
    }
    #[doc = "Bits 4:5 - Period of probe"]
    #[inline(always)]
    #[must_use]
    pub fn perpr(&mut self) -> PerprW<AdpctlSpec> {
        PerprW::new(self, 4)
    }
    #[doc = "Bit 17 - ADP probe enable"]
    #[inline(always)]
    #[must_use]
    pub fn pren(&mut self) -> PrenW<AdpctlSpec> {
        PrenW::new(self, 17)
    }
    #[doc = "Bit 18 - ADP sense enable"]
    #[inline(always)]
    #[must_use]
    pub fn snen(&mut self) -> SnenW<AdpctlSpec> {
        SnenW::new(self, 18)
    }
    #[doc = "Bit 20 - ADP enable"]
    #[inline(always)]
    #[must_use]
    pub fn adpen(&mut self) -> AdpenW<AdpctlSpec> {
        AdpenW::new(self, 20)
    }
    #[doc = "Bit 21 - ADP probe interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn adpprf(&mut self) -> AdpprfW<AdpctlSpec> {
        AdpprfW::new(self, 21)
    }
    #[doc = "Bit 22 - ADP sense interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn adpsnf(&mut self) -> AdpsnfW<AdpctlSpec> {
        AdpsnfW::new(self, 22)
    }
    #[doc = "Bit 23 - ADP timeout interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn adptf(&mut self) -> AdptfW<AdpctlSpec> {
        AdptfW::new(self, 23)
    }
    #[doc = "Bit 24 - The mask of ADP probe interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn adpprfm(&mut self) -> AdpprfmW<AdpctlSpec> {
        AdpprfmW::new(self, 24)
    }
    #[doc = "Bit 25 - The mask of ADP sense interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn adpsnfm(&mut self) -> AdpsnfmW<AdpctlSpec> {
        AdpsnfmW::new(self, 25)
    }
    #[doc = "Bit 26 - The mask of ADP timeout interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn adptfm(&mut self) -> AdptfmW<AdpctlSpec> {
        AdptfmW::new(self, 26)
    }
    #[doc = "Bits 27:28 - Read and write request"]
    #[inline(always)]
    #[must_use]
    pub fn rwr(&mut self) -> RwrW<AdpctlSpec> {
        RwrW::new(self, 27)
    }
}
#[doc = "ADP control andstatus register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`adpctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`adpctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AdpctlSpec;
impl crate::RegisterSpec for AdpctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`adpctl::R`](R) reader structure"]
impl crate::Readable for AdpctlSpec {}
#[doc = "`write(|w| ..)` method takes [`adpctl::W`](W) writer structure"]
impl crate::Writable for AdpctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ADPCTL to value 0x1000"]
impl crate::Resettable for AdpctlSpec {
    const RESET_VALUE: u32 = 0x1000;
}
