#[doc = "Register `PERI_BACKUP_INT_RAW` reader"]
pub type R = crate::R<PERI_BACKUP_INT_RAW_SPEC>;
#[doc = "Field `DONE` reader - reg_peri_backup_done_int_raw"]
pub type DONE_R = crate::BitReader;
#[doc = "Field `ERR` reader - reg_peri_backup_err_int_raw"]
pub type ERR_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - reg_peri_backup_done_int_raw"]
    #[inline(always)]
    pub fn done(&self) -> DONE_R {
        DONE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - reg_peri_backup_err_int_raw"]
    #[inline(always)]
    pub fn err(&self) -> ERR_R {
        ERR_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PERI_BACKUP_INT_RAW")
            .field("done", &self.done())
            .field("err", &self.err())
            .finish()
    }
}
#[doc = "APB_CTRL_PERI_BACKUP_INT_RAW_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`peri_backup_int_raw::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PERI_BACKUP_INT_RAW_SPEC;
impl crate::RegisterSpec for PERI_BACKUP_INT_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`peri_backup_int_raw::R`](R) reader structure"]
impl crate::Readable for PERI_BACKUP_INT_RAW_SPEC {}
#[doc = "`reset()` method sets PERI_BACKUP_INT_RAW to value 0"]
impl crate::Resettable for PERI_BACKUP_INT_RAW_SPEC {}
