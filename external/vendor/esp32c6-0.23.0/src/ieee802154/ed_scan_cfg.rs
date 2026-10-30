#[doc = "Register `ED_SCAN_CFG` reader"]
pub type R = crate::R<ED_SCAN_CFG_SPEC>;
#[doc = "Register `ED_SCAN_CFG` writer"]
pub type W = crate::W<ED_SCAN_CFG_SPEC>;
#[doc = "Field `CCA_ED_THRESHOLD` reader - "]
pub type CCA_ED_THRESHOLD_R = crate::FieldReader;
#[doc = "Field `CCA_ED_THRESHOLD` writer - "]
pub type CCA_ED_THRESHOLD_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `ED_SAMPLE_MODE` reader - "]
pub type ED_SAMPLE_MODE_R = crate::FieldReader;
#[doc = "Field `ED_SAMPLE_MODE` writer - "]
pub type ED_SAMPLE_MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `DIS_ED_POWER_SEL` reader - "]
pub type DIS_ED_POWER_SEL_R = crate::BitReader;
#[doc = "Field `DIS_ED_POWER_SEL` writer - "]
pub type DIS_ED_POWER_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CCA_MODE` reader - "]
pub type CCA_MODE_R = crate::FieldReader;
#[doc = "Field `CCA_MODE` writer - "]
pub type CCA_MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `ED_RSS` reader - "]
pub type ED_RSS_R = crate::FieldReader;
#[doc = "Field `ED_RSS` writer - "]
pub type ED_RSS_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `CCA_BUSY` reader - "]
pub type CCA_BUSY_R = crate::BitReader;
#[doc = "Field `CCA_BUSY` writer - "]
pub type CCA_BUSY_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:7"]
    #[inline(always)]
    pub fn cca_ed_threshold(&self) -> CCA_ED_THRESHOLD_R {
        CCA_ED_THRESHOLD_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 11:12"]
    #[inline(always)]
    pub fn ed_sample_mode(&self) -> ED_SAMPLE_MODE_R {
        ED_SAMPLE_MODE_R::new(((self.bits >> 11) & 3) as u8)
    }
    #[doc = "Bit 13"]
    #[inline(always)]
    pub fn dis_ed_power_sel(&self) -> DIS_ED_POWER_SEL_R {
        DIS_ED_POWER_SEL_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bits 14:15"]
    #[inline(always)]
    pub fn cca_mode(&self) -> CCA_MODE_R {
        CCA_MODE_R::new(((self.bits >> 14) & 3) as u8)
    }
    #[doc = "Bits 16:23"]
    #[inline(always)]
    pub fn ed_rss(&self) -> ED_RSS_R {
        ED_RSS_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bit 24"]
    #[inline(always)]
    pub fn cca_busy(&self) -> CCA_BUSY_R {
        CCA_BUSY_R::new(((self.bits >> 24) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ED_SCAN_CFG")
            .field("cca_ed_threshold", &self.cca_ed_threshold())
            .field("ed_sample_mode", &self.ed_sample_mode())
            .field("dis_ed_power_sel", &self.dis_ed_power_sel())
            .field("cca_mode", &self.cca_mode())
            .field("ed_rss", &self.ed_rss())
            .field("cca_busy", &self.cca_busy())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7"]
    #[inline(always)]
    pub fn cca_ed_threshold(&mut self) -> CCA_ED_THRESHOLD_W<'_, ED_SCAN_CFG_SPEC> {
        CCA_ED_THRESHOLD_W::new(self, 0)
    }
    #[doc = "Bits 11:12"]
    #[inline(always)]
    pub fn ed_sample_mode(&mut self) -> ED_SAMPLE_MODE_W<'_, ED_SCAN_CFG_SPEC> {
        ED_SAMPLE_MODE_W::new(self, 11)
    }
    #[doc = "Bit 13"]
    #[inline(always)]
    pub fn dis_ed_power_sel(&mut self) -> DIS_ED_POWER_SEL_W<'_, ED_SCAN_CFG_SPEC> {
        DIS_ED_POWER_SEL_W::new(self, 13)
    }
    #[doc = "Bits 14:15"]
    #[inline(always)]
    pub fn cca_mode(&mut self) -> CCA_MODE_W<'_, ED_SCAN_CFG_SPEC> {
        CCA_MODE_W::new(self, 14)
    }
    #[doc = "Bits 16:23"]
    #[inline(always)]
    pub fn ed_rss(&mut self) -> ED_RSS_W<'_, ED_SCAN_CFG_SPEC> {
        ED_RSS_W::new(self, 16)
    }
    #[doc = "Bit 24"]
    #[inline(always)]
    pub fn cca_busy(&mut self) -> CCA_BUSY_W<'_, ED_SCAN_CFG_SPEC> {
        CCA_BUSY_W::new(self, 24)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`ed_scan_cfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ed_scan_cfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ED_SCAN_CFG_SPEC;
impl crate::RegisterSpec for ED_SCAN_CFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ed_scan_cfg::R`](R) reader structure"]
impl crate::Readable for ED_SCAN_CFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ed_scan_cfg::W`](W) writer structure"]
impl crate::Writable for ED_SCAN_CFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ED_SCAN_CFG to value 0"]
impl crate::Resettable for ED_SCAN_CFG_SPEC {}
