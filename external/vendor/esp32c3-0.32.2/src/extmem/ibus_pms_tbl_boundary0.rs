#[doc = "Register `IBUS_PMS_TBL_BOUNDARY0` reader"]
pub type R = crate::R<IBUS_PMS_TBL_BOUNDARY0_SPEC>;
#[doc = "Register `IBUS_PMS_TBL_BOUNDARY0` writer"]
pub type W = crate::W<IBUS_PMS_TBL_BOUNDARY0_SPEC>;
#[doc = "Field `IBUS_PMS_BOUNDARY0` reader - The bit is used to configure the ibus permission control section boundary0"]
pub type IBUS_PMS_BOUNDARY0_R = crate::FieldReader<u16>;
#[doc = "Field `IBUS_PMS_BOUNDARY0` writer - The bit is used to configure the ibus permission control section boundary0"]
pub type IBUS_PMS_BOUNDARY0_W<'a, REG> = crate::FieldWriter<'a, REG, 12, u16>;
impl R {
    #[doc = "Bits 0:11 - The bit is used to configure the ibus permission control section boundary0"]
    #[inline(always)]
    pub fn ibus_pms_boundary0(&self) -> IBUS_PMS_BOUNDARY0_R {
        IBUS_PMS_BOUNDARY0_R::new((self.bits & 0x0fff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IBUS_PMS_TBL_BOUNDARY0")
            .field("ibus_pms_boundary0", &self.ibus_pms_boundary0())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:11 - The bit is used to configure the ibus permission control section boundary0"]
    #[inline(always)]
    pub fn ibus_pms_boundary0(&mut self) -> IBUS_PMS_BOUNDARY0_W<'_, IBUS_PMS_TBL_BOUNDARY0_SPEC> {
        IBUS_PMS_BOUNDARY0_W::new(self, 0)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`ibus_pms_tbl_boundary0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ibus_pms_tbl_boundary0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IBUS_PMS_TBL_BOUNDARY0_SPEC;
impl crate::RegisterSpec for IBUS_PMS_TBL_BOUNDARY0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ibus_pms_tbl_boundary0::R`](R) reader structure"]
impl crate::Readable for IBUS_PMS_TBL_BOUNDARY0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ibus_pms_tbl_boundary0::W`](W) writer structure"]
impl crate::Writable for IBUS_PMS_TBL_BOUNDARY0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IBUS_PMS_TBL_BOUNDARY0 to value 0"]
impl crate::Resettable for IBUS_PMS_TBL_BOUNDARY0_SPEC {}
