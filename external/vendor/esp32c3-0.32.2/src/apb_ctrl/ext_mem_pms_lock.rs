#[doc = "Register `EXT_MEM_PMS_LOCK` reader"]
pub type R = crate::R<EXT_MEM_PMS_LOCK_SPEC>;
#[doc = "Register `EXT_MEM_PMS_LOCK` writer"]
pub type W = crate::W<EXT_MEM_PMS_LOCK_SPEC>;
#[doc = "Field `EXT_MEM_PMS_LOCK` reader - reg_ext_mem_pms_lock"]
pub type EXT_MEM_PMS_LOCK_R = crate::BitReader;
#[doc = "Field `EXT_MEM_PMS_LOCK` writer - reg_ext_mem_pms_lock"]
pub type EXT_MEM_PMS_LOCK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - reg_ext_mem_pms_lock"]
    #[inline(always)]
    pub fn ext_mem_pms_lock(&self) -> EXT_MEM_PMS_LOCK_R {
        EXT_MEM_PMS_LOCK_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("EXT_MEM_PMS_LOCK")
            .field("ext_mem_pms_lock", &self.ext_mem_pms_lock())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - reg_ext_mem_pms_lock"]
    #[inline(always)]
    pub fn ext_mem_pms_lock(&mut self) -> EXT_MEM_PMS_LOCK_W<'_, EXT_MEM_PMS_LOCK_SPEC> {
        EXT_MEM_PMS_LOCK_W::new(self, 0)
    }
}
#[doc = "APB_CTRL_EXT_MEM_PMS_LOCK_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`ext_mem_pms_lock::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ext_mem_pms_lock::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct EXT_MEM_PMS_LOCK_SPEC;
impl crate::RegisterSpec for EXT_MEM_PMS_LOCK_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ext_mem_pms_lock::R`](R) reader structure"]
impl crate::Readable for EXT_MEM_PMS_LOCK_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ext_mem_pms_lock::W`](W) writer structure"]
impl crate::Writable for EXT_MEM_PMS_LOCK_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets EXT_MEM_PMS_LOCK to value 0"]
impl crate::Resettable for EXT_MEM_PMS_LOCK_SPEC {}
