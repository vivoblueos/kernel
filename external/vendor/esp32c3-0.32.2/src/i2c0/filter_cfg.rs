#[doc = "Register `FILTER_CFG` reader"]
pub type R = crate::R<FILTER_CFG_SPEC>;
#[doc = "Register `FILTER_CFG` writer"]
pub type W = crate::W<FILTER_CFG_SPEC>;
#[doc = "Field `SCL_FILTER_THRES` reader - reg_scl_filter_thres"]
pub type SCL_FILTER_THRES_R = crate::FieldReader;
#[doc = "Field `SCL_FILTER_THRES` writer - reg_scl_filter_thres"]
pub type SCL_FILTER_THRES_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `SDA_FILTER_THRES` reader - reg_sda_filter_thres"]
pub type SDA_FILTER_THRES_R = crate::FieldReader;
#[doc = "Field `SDA_FILTER_THRES` writer - reg_sda_filter_thres"]
pub type SDA_FILTER_THRES_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `SCL_FILTER_EN` reader - reg_scl_filter_en"]
pub type SCL_FILTER_EN_R = crate::BitReader;
#[doc = "Field `SCL_FILTER_EN` writer - reg_scl_filter_en"]
pub type SCL_FILTER_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDA_FILTER_EN` reader - reg_sda_filter_en"]
pub type SDA_FILTER_EN_R = crate::BitReader;
#[doc = "Field `SDA_FILTER_EN` writer - reg_sda_filter_en"]
pub type SDA_FILTER_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:3 - reg_scl_filter_thres"]
    #[inline(always)]
    pub fn scl_filter_thres(&self) -> SCL_FILTER_THRES_R {
        SCL_FILTER_THRES_R::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:7 - reg_sda_filter_thres"]
    #[inline(always)]
    pub fn sda_filter_thres(&self) -> SDA_FILTER_THRES_R {
        SDA_FILTER_THRES_R::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bit 8 - reg_scl_filter_en"]
    #[inline(always)]
    pub fn scl_filter_en(&self) -> SCL_FILTER_EN_R {
        SCL_FILTER_EN_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - reg_sda_filter_en"]
    #[inline(always)]
    pub fn sda_filter_en(&self) -> SDA_FILTER_EN_R {
        SDA_FILTER_EN_R::new(((self.bits >> 9) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FILTER_CFG")
            .field("scl_filter_thres", &self.scl_filter_thres())
            .field("sda_filter_thres", &self.sda_filter_thres())
            .field("scl_filter_en", &self.scl_filter_en())
            .field("sda_filter_en", &self.sda_filter_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3 - reg_scl_filter_thres"]
    #[inline(always)]
    pub fn scl_filter_thres(&mut self) -> SCL_FILTER_THRES_W<'_, FILTER_CFG_SPEC> {
        SCL_FILTER_THRES_W::new(self, 0)
    }
    #[doc = "Bits 4:7 - reg_sda_filter_thres"]
    #[inline(always)]
    pub fn sda_filter_thres(&mut self) -> SDA_FILTER_THRES_W<'_, FILTER_CFG_SPEC> {
        SDA_FILTER_THRES_W::new(self, 4)
    }
    #[doc = "Bit 8 - reg_scl_filter_en"]
    #[inline(always)]
    pub fn scl_filter_en(&mut self) -> SCL_FILTER_EN_W<'_, FILTER_CFG_SPEC> {
        SCL_FILTER_EN_W::new(self, 8)
    }
    #[doc = "Bit 9 - reg_sda_filter_en"]
    #[inline(always)]
    pub fn sda_filter_en(&mut self) -> SDA_FILTER_EN_W<'_, FILTER_CFG_SPEC> {
        SDA_FILTER_EN_W::new(self, 9)
    }
}
#[doc = "I2C_FILTER_CFG_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`filter_cfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`filter_cfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FILTER_CFG_SPEC;
impl crate::RegisterSpec for FILTER_CFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`filter_cfg::R`](R) reader structure"]
impl crate::Readable for FILTER_CFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`filter_cfg::W`](W) writer structure"]
impl crate::Writable for FILTER_CFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FILTER_CFG to value 0x0300"]
impl crate::Resettable for FILTER_CFG_SPEC {
    const RESET_VALUE: u32 = 0x0300;
}
