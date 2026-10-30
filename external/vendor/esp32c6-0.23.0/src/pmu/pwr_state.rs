#[doc = "Register `PWR_STATE` reader"]
pub type R = crate::R<PWR_STATE_SPEC>;
#[doc = "Field `BACKUP_ST_STATE` reader - need_des"]
pub type BACKUP_ST_STATE_R = crate::FieldReader;
#[doc = "Field `LP_PWR_ST_STATE` reader - need_des"]
pub type LP_PWR_ST_STATE_R = crate::FieldReader;
#[doc = "Field `HP_PWR_ST_STATE` reader - need_des"]
pub type HP_PWR_ST_STATE_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 13:17 - need_des"]
    #[inline(always)]
    pub fn backup_st_state(&self) -> BACKUP_ST_STATE_R {
        BACKUP_ST_STATE_R::new(((self.bits >> 13) & 0x1f) as u8)
    }
    #[doc = "Bits 18:22 - need_des"]
    #[inline(always)]
    pub fn lp_pwr_st_state(&self) -> LP_PWR_ST_STATE_R {
        LP_PWR_ST_STATE_R::new(((self.bits >> 18) & 0x1f) as u8)
    }
    #[doc = "Bits 23:31 - need_des"]
    #[inline(always)]
    pub fn hp_pwr_st_state(&self) -> HP_PWR_ST_STATE_R {
        HP_PWR_ST_STATE_R::new(((self.bits >> 23) & 0x01ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PWR_STATE")
            .field("backup_st_state", &self.backup_st_state())
            .field("lp_pwr_st_state", &self.lp_pwr_st_state())
            .field("hp_pwr_st_state", &self.hp_pwr_st_state())
            .finish()
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`pwr_state::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PWR_STATE_SPEC;
impl crate::RegisterSpec for PWR_STATE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pwr_state::R`](R) reader structure"]
impl crate::Readable for PWR_STATE_SPEC {}
#[doc = "`reset()` method sets PWR_STATE to value 0x0080_2000"]
impl crate::Resettable for PWR_STATE_SPEC {
    const RESET_VALUE: u32 = 0x0080_2000;
}
