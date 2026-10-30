#[doc = "Register `SCL_SP_CONF` reader"]
pub type R = crate::R<SCL_SP_CONF_SPEC>;
#[doc = "Register `SCL_SP_CONF` writer"]
pub type W = crate::W<SCL_SP_CONF_SPEC>;
#[doc = "Field `SCL_RST_SLV_EN` reader - reg_scl_rst_slv_en"]
pub type SCL_RST_SLV_EN_R = crate::BitReader;
#[doc = "Field `SCL_RST_SLV_EN` writer - reg_scl_rst_slv_en"]
pub type SCL_RST_SLV_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SCL_RST_SLV_NUM` reader - reg_scl_rst_slv_num"]
pub type SCL_RST_SLV_NUM_R = crate::FieldReader;
#[doc = "Field `SCL_RST_SLV_NUM` writer - reg_scl_rst_slv_num"]
pub type SCL_RST_SLV_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `SCL_PD_EN` reader - reg_scl_pd_en"]
pub type SCL_PD_EN_R = crate::BitReader;
#[doc = "Field `SCL_PD_EN` writer - reg_scl_pd_en"]
pub type SCL_PD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDA_PD_EN` reader - reg_sda_pd_en"]
pub type SDA_PD_EN_R = crate::BitReader;
#[doc = "Field `SDA_PD_EN` writer - reg_sda_pd_en"]
pub type SDA_PD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - reg_scl_rst_slv_en"]
    #[inline(always)]
    pub fn scl_rst_slv_en(&self) -> SCL_RST_SLV_EN_R {
        SCL_RST_SLV_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:5 - reg_scl_rst_slv_num"]
    #[inline(always)]
    pub fn scl_rst_slv_num(&self) -> SCL_RST_SLV_NUM_R {
        SCL_RST_SLV_NUM_R::new(((self.bits >> 1) & 0x1f) as u8)
    }
    #[doc = "Bit 6 - reg_scl_pd_en"]
    #[inline(always)]
    pub fn scl_pd_en(&self) -> SCL_PD_EN_R {
        SCL_PD_EN_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - reg_sda_pd_en"]
    #[inline(always)]
    pub fn sda_pd_en(&self) -> SDA_PD_EN_R {
        SDA_PD_EN_R::new(((self.bits >> 7) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SCL_SP_CONF")
            .field("scl_rst_slv_en", &self.scl_rst_slv_en())
            .field("scl_rst_slv_num", &self.scl_rst_slv_num())
            .field("scl_pd_en", &self.scl_pd_en())
            .field("sda_pd_en", &self.sda_pd_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - reg_scl_rst_slv_en"]
    #[inline(always)]
    pub fn scl_rst_slv_en(&mut self) -> SCL_RST_SLV_EN_W<'_, SCL_SP_CONF_SPEC> {
        SCL_RST_SLV_EN_W::new(self, 0)
    }
    #[doc = "Bits 1:5 - reg_scl_rst_slv_num"]
    #[inline(always)]
    pub fn scl_rst_slv_num(&mut self) -> SCL_RST_SLV_NUM_W<'_, SCL_SP_CONF_SPEC> {
        SCL_RST_SLV_NUM_W::new(self, 1)
    }
    #[doc = "Bit 6 - reg_scl_pd_en"]
    #[inline(always)]
    pub fn scl_pd_en(&mut self) -> SCL_PD_EN_W<'_, SCL_SP_CONF_SPEC> {
        SCL_PD_EN_W::new(self, 6)
    }
    #[doc = "Bit 7 - reg_sda_pd_en"]
    #[inline(always)]
    pub fn sda_pd_en(&mut self) -> SDA_PD_EN_W<'_, SCL_SP_CONF_SPEC> {
        SDA_PD_EN_W::new(self, 7)
    }
}
#[doc = "I2C_SCL_SP_CONF_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_sp_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_sp_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SCL_SP_CONF_SPEC;
impl crate::RegisterSpec for SCL_SP_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`scl_sp_conf::R`](R) reader structure"]
impl crate::Readable for SCL_SP_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`scl_sp_conf::W`](W) writer structure"]
impl crate::Writable for SCL_SP_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SCL_SP_CONF to value 0"]
impl crate::Resettable for SCL_SP_CONF_SPEC {}
