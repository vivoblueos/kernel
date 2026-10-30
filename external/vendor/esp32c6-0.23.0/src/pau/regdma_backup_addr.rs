#[doc = "Register `REGDMA_BACKUP_ADDR` reader"]
pub type R = crate::R<REGDMA_BACKUP_ADDR_SPEC>;
#[doc = "Field `BACKUP_ADDR` reader - backup addr reg"]
pub type BACKUP_ADDR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - backup addr reg"]
    #[inline(always)]
    pub fn backup_addr(&self) -> BACKUP_ADDR_R {
        BACKUP_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("REGDMA_BACKUP_ADDR")
            .field("backup_addr", &self.backup_addr())
            .finish()
    }
}
#[doc = "Backup addr\n\nYou can [`read`](crate::Reg::read) this register and get [`regdma_backup_addr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REGDMA_BACKUP_ADDR_SPEC;
impl crate::RegisterSpec for REGDMA_BACKUP_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`regdma_backup_addr::R`](R) reader structure"]
impl crate::Readable for REGDMA_BACKUP_ADDR_SPEC {}
#[doc = "`reset()` method sets REGDMA_BACKUP_ADDR to value 0"]
impl crate::Resettable for REGDMA_BACKUP_ADDR_SPEC {}
