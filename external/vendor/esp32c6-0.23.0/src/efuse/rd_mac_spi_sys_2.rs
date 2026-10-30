#[doc = "Register `RD_MAC_SPI_SYS_2` reader"]
pub type R = crate::R<RD_MAC_SPI_SYS_2_SPEC>;
#[doc = "Field `ACTIVE_HP_DBIAS` reader - Stores the active hp dbias."]
pub type ACTIVE_HP_DBIAS_R = crate::FieldReader;
#[doc = "Field `ACTIVE_LP_DBIAS` reader - Stores the active lp dbias."]
pub type ACTIVE_LP_DBIAS_R = crate::FieldReader;
#[doc = "Field `LSLP_HP_DBG` reader - Stores the lslp hp dbg."]
pub type LSLP_HP_DBG_R = crate::FieldReader;
#[doc = "Field `LSLP_HP_DBIAS` reader - Stores the lslp hp dbias."]
pub type LSLP_HP_DBIAS_R = crate::FieldReader;
#[doc = "Field `DSLP_LP_DBG` reader - Stores the dslp lp dbg."]
pub type DSLP_LP_DBG_R = crate::FieldReader;
#[doc = "Field `DSLP_LP_DBIAS` reader - Stores the dslp lp dbias."]
pub type DSLP_LP_DBIAS_R = crate::FieldReader;
#[doc = "Field `DBIAS_VOL_GAP` reader - Stores the hp and lp dbias vol gap."]
pub type DBIAS_VOL_GAP_R = crate::FieldReader;
#[doc = "Field `SPI_PAD_CONF_1` reader - Reserved."]
pub type SPI_PAD_CONF_1_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:4 - Stores the active hp dbias."]
    #[inline(always)]
    pub fn active_hp_dbias(&self) -> ACTIVE_HP_DBIAS_R {
        ACTIVE_HP_DBIAS_R::new((self.bits & 0x1f) as u8)
    }
    #[doc = "Bits 5:9 - Stores the active lp dbias."]
    #[inline(always)]
    pub fn active_lp_dbias(&self) -> ACTIVE_LP_DBIAS_R {
        ACTIVE_LP_DBIAS_R::new(((self.bits >> 5) & 0x1f) as u8)
    }
    #[doc = "Bits 10:11 - Stores the lslp hp dbg."]
    #[inline(always)]
    pub fn lslp_hp_dbg(&self) -> LSLP_HP_DBG_R {
        LSLP_HP_DBG_R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bits 12:15 - Stores the lslp hp dbias."]
    #[inline(always)]
    pub fn lslp_hp_dbias(&self) -> LSLP_HP_DBIAS_R {
        LSLP_HP_DBIAS_R::new(((self.bits >> 12) & 0x0f) as u8)
    }
    #[doc = "Bits 16:18 - Stores the dslp lp dbg."]
    #[inline(always)]
    pub fn dslp_lp_dbg(&self) -> DSLP_LP_DBG_R {
        DSLP_LP_DBG_R::new(((self.bits >> 16) & 7) as u8)
    }
    #[doc = "Bits 19:22 - Stores the dslp lp dbias."]
    #[inline(always)]
    pub fn dslp_lp_dbias(&self) -> DSLP_LP_DBIAS_R {
        DSLP_LP_DBIAS_R::new(((self.bits >> 19) & 0x0f) as u8)
    }
    #[doc = "Bits 23:27 - Stores the hp and lp dbias vol gap."]
    #[inline(always)]
    pub fn dbias_vol_gap(&self) -> DBIAS_VOL_GAP_R {
        DBIAS_VOL_GAP_R::new(((self.bits >> 23) & 0x1f) as u8)
    }
    #[doc = "Bits 28:31 - Reserved."]
    #[inline(always)]
    pub fn spi_pad_conf_1(&self) -> SPI_PAD_CONF_1_R {
        SPI_PAD_CONF_1_R::new(((self.bits >> 28) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_MAC_SPI_SYS_2")
            .field("active_hp_dbias", &self.active_hp_dbias())
            .field("active_lp_dbias", &self.active_lp_dbias())
            .field("lslp_hp_dbg", &self.lslp_hp_dbg())
            .field("lslp_hp_dbias", &self.lslp_hp_dbias())
            .field("dslp_lp_dbg", &self.dslp_lp_dbg())
            .field("dslp_lp_dbias", &self.dslp_lp_dbias())
            .field("dbias_vol_gap", &self.dbias_vol_gap())
            .field("spi_pad_conf_1", &self.spi_pad_conf_1())
            .finish()
    }
}
#[doc = "BLOCK1 data register $n.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_mac_spi_sys_2::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_MAC_SPI_SYS_2_SPEC;
impl crate::RegisterSpec for RD_MAC_SPI_SYS_2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_mac_spi_sys_2::R`](R) reader structure"]
impl crate::Readable for RD_MAC_SPI_SYS_2_SPEC {}
#[doc = "`reset()` method sets RD_MAC_SPI_SYS_2 to value 0"]
impl crate::Resettable for RD_MAC_SPI_SYS_2_SPEC {}
