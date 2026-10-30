#[doc = "Register `PERI_BACKUP_INT_CLR` writer"]
pub type W = crate::W<PERI_BACKUP_INT_CLR_SPEC>;
#[doc = "Field `DONE` writer - reg_peri_backup_done_int_clr"]
pub type DONE_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `ERR` writer - reg_peri_backup_err_int_clr"]
pub type ERR_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<PERI_BACKUP_INT_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - reg_peri_backup_done_int_clr"]
    #[inline(always)]
    pub fn done(&mut self) -> DONE_W<'_, PERI_BACKUP_INT_CLR_SPEC> {
        DONE_W::new(self, 0)
    }
    #[doc = "Bit 1 - reg_peri_backup_err_int_clr"]
    #[inline(always)]
    pub fn err(&mut self) -> ERR_W<'_, PERI_BACKUP_INT_CLR_SPEC> {
        ERR_W::new(self, 1)
    }
}
#[doc = "APB_CTRL_PERI_BACKUP_INT_CLR_REG\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`peri_backup_int_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PERI_BACKUP_INT_CLR_SPEC;
impl crate::RegisterSpec for PERI_BACKUP_INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`peri_backup_int_clr::W`](W) writer structure"]
impl crate::Writable for PERI_BACKUP_INT_CLR_SPEC {
    type Safety = crate::Unsafe;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0x03;
}
#[doc = "`reset()` method sets PERI_BACKUP_INT_CLR to value 0"]
impl crate::Resettable for PERI_BACKUP_INT_CLR_SPEC {}
