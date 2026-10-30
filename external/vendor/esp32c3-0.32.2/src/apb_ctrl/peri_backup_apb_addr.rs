#[doc = "Register `PERI_BACKUP_APB_ADDR` reader"]
pub type R = crate::R<PERI_BACKUP_APB_ADDR_SPEC>;
#[doc = "Register `PERI_BACKUP_APB_ADDR` writer"]
pub type W = crate::W<PERI_BACKUP_APB_ADDR_SPEC>;
#[doc = "Field `BACKUP_APB_START_ADDR` reader - reg_backup_apb_start_addr"]
pub type BACKUP_APB_START_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `BACKUP_APB_START_ADDR` writer - reg_backup_apb_start_addr"]
pub type BACKUP_APB_START_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - reg_backup_apb_start_addr"]
    #[inline(always)]
    pub fn backup_apb_start_addr(&self) -> BACKUP_APB_START_ADDR_R {
        BACKUP_APB_START_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PERI_BACKUP_APB_ADDR")
            .field("backup_apb_start_addr", &self.backup_apb_start_addr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - reg_backup_apb_start_addr"]
    #[inline(always)]
    pub fn backup_apb_start_addr(
        &mut self,
    ) -> BACKUP_APB_START_ADDR_W<'_, PERI_BACKUP_APB_ADDR_SPEC> {
        BACKUP_APB_START_ADDR_W::new(self, 0)
    }
}
#[doc = "APB_CTRL_PERI_BACKUP_APB_ADDR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`peri_backup_apb_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`peri_backup_apb_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PERI_BACKUP_APB_ADDR_SPEC;
impl crate::RegisterSpec for PERI_BACKUP_APB_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`peri_backup_apb_addr::R`](R) reader structure"]
impl crate::Readable for PERI_BACKUP_APB_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`peri_backup_apb_addr::W`](W) writer structure"]
impl crate::Writable for PERI_BACKUP_APB_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PERI_BACKUP_APB_ADDR to value 0"]
impl crate::Resettable for PERI_BACKUP_APB_ADDR_SPEC {}
