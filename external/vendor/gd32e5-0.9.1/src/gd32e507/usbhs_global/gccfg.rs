#[doc = "Register `GCCFG` reader"]
pub type R = crate::R<GccfgSpec>;
#[doc = "Register `GCCFG` writer"]
pub type W = crate::W<GccfgSpec>;
#[doc = "Field `DCDF` reader - Data connect detection status"]
pub type DcdfR = crate::BitReader;
#[doc = "Field `DCDF` writer - Data connect detection status"]
pub type DcdfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PDF` reader - Primary detection status"]
pub type PdfR = crate::BitReader;
#[doc = "Field `PDF` writer - Primary detection status"]
pub type PdfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDF` reader - Secondary detection status"]
pub type SdfR = crate::BitReader;
#[doc = "Field `SDF` writer - Secondary detection status"]
pub type SdfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PS2F` reader - PS2 detection status"]
pub type Ps2fR = crate::BitReader;
#[doc = "Field `PS2F` writer - PS2 detection status"]
pub type Ps2fW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BCDEN` reader - Battery charging detection enable"]
pub type BcdenR = crate::BitReader;
#[doc = "Field `BCDEN` writer - Battery charging detection enable"]
pub type BcdenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DCDMEN` reader - Data connect detection mode enable"]
pub type DcdmenR = crate::BitReader;
#[doc = "Field `DCDMEN` writer - Data connect detection mode enable"]
pub type DcdmenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PDMEN` reader - Primary detection mode enable"]
pub type PdmenR = crate::BitReader;
#[doc = "Field `PDMEN` writer - Primary detection mode enable"]
pub type PdmenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDMEN` reader - Secondary detection mode enable"]
pub type SdmenR = crate::BitReader;
#[doc = "Field `SDMEN` writer - Secondary detection mode enable"]
pub type SdmenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PWRON` reader - Power on"]
pub type PwronR = crate::BitReader;
#[doc = "Field `PWRON` writer - Power on"]
pub type PwronW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SOFOEN` reader - SOF output enable"]
pub type SofoenR = crate::BitReader;
#[doc = "Field `SOFOEN` writer - SOF output enable"]
pub type SofoenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `VDEN` reader - Enable of VBUS sensing comparator to detect VBUS valid"]
pub type VdenR = crate::BitReader;
#[doc = "Field `VDEN` writer - Enable of VBUS sensing comparator to detect VBUS valid"]
pub type VdenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Data connect detection status"]
    #[inline(always)]
    pub fn dcdf(&self) -> DcdfR {
        DcdfR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Primary detection status"]
    #[inline(always)]
    pub fn pdf(&self) -> PdfR {
        PdfR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Secondary detection status"]
    #[inline(always)]
    pub fn sdf(&self) -> SdfR {
        SdfR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - PS2 detection status"]
    #[inline(always)]
    pub fn ps2f(&self) -> Ps2fR {
        Ps2fR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 12 - Battery charging detection enable"]
    #[inline(always)]
    pub fn bcden(&self) -> BcdenR {
        BcdenR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Data connect detection mode enable"]
    #[inline(always)]
    pub fn dcdmen(&self) -> DcdmenR {
        DcdmenR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Primary detection mode enable"]
    #[inline(always)]
    pub fn pdmen(&self) -> PdmenR {
        PdmenR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Secondary detection mode enable"]
    #[inline(always)]
    pub fn sdmen(&self) -> SdmenR {
        SdmenR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Power on"]
    #[inline(always)]
    pub fn pwron(&self) -> PwronR {
        PwronR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 20 - SOF output enable"]
    #[inline(always)]
    pub fn sofoen(&self) -> SofoenR {
        SofoenR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Enable of VBUS sensing comparator to detect VBUS valid"]
    #[inline(always)]
    pub fn vden(&self) -> VdenR {
        VdenR::new(((self.bits >> 21) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Data connect detection status"]
    #[inline(always)]
    #[must_use]
    pub fn dcdf(&mut self) -> DcdfW<GccfgSpec> {
        DcdfW::new(self, 0)
    }
    #[doc = "Bit 1 - Primary detection status"]
    #[inline(always)]
    #[must_use]
    pub fn pdf(&mut self) -> PdfW<GccfgSpec> {
        PdfW::new(self, 1)
    }
    #[doc = "Bit 2 - Secondary detection status"]
    #[inline(always)]
    #[must_use]
    pub fn sdf(&mut self) -> SdfW<GccfgSpec> {
        SdfW::new(self, 2)
    }
    #[doc = "Bit 3 - PS2 detection status"]
    #[inline(always)]
    #[must_use]
    pub fn ps2f(&mut self) -> Ps2fW<GccfgSpec> {
        Ps2fW::new(self, 3)
    }
    #[doc = "Bit 12 - Battery charging detection enable"]
    #[inline(always)]
    #[must_use]
    pub fn bcden(&mut self) -> BcdenW<GccfgSpec> {
        BcdenW::new(self, 12)
    }
    #[doc = "Bit 13 - Data connect detection mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn dcdmen(&mut self) -> DcdmenW<GccfgSpec> {
        DcdmenW::new(self, 13)
    }
    #[doc = "Bit 14 - Primary detection mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn pdmen(&mut self) -> PdmenW<GccfgSpec> {
        PdmenW::new(self, 14)
    }
    #[doc = "Bit 15 - Secondary detection mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn sdmen(&mut self) -> SdmenW<GccfgSpec> {
        SdmenW::new(self, 15)
    }
    #[doc = "Bit 16 - Power on"]
    #[inline(always)]
    #[must_use]
    pub fn pwron(&mut self) -> PwronW<GccfgSpec> {
        PwronW::new(self, 16)
    }
    #[doc = "Bit 20 - SOF output enable"]
    #[inline(always)]
    #[must_use]
    pub fn sofoen(&mut self) -> SofoenW<GccfgSpec> {
        SofoenW::new(self, 20)
    }
    #[doc = "Bit 21 - Enable of VBUS sensing comparator to detect VBUS valid"]
    #[inline(always)]
    #[must_use]
    pub fn vden(&mut self) -> VdenW<GccfgSpec> {
        VdenW::new(self, 21)
    }
}
#[doc = "Global core configuration register (USBFS_GCCFG)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`gccfg::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`gccfg::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GccfgSpec;
impl crate::RegisterSpec for GccfgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`gccfg::R`](R) reader structure"]
impl crate::Readable for GccfgSpec {}
#[doc = "`write(|w| ..)` method takes [`gccfg::W`](W) writer structure"]
impl crate::Writable for GccfgSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets GCCFG to value 0"]
impl crate::Resettable for GccfgSpec {
    const RESET_VALUE: u32 = 0;
}
