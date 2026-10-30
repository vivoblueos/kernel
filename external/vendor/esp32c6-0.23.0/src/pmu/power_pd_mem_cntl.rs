#[doc = "Register `POWER_PD_MEM_CNTL` reader"]
pub type R = crate::R<POWER_PD_MEM_CNTL_SPEC>;
#[doc = "Register `POWER_PD_MEM_CNTL` writer"]
pub type W = crate::W<POWER_PD_MEM_CNTL_SPEC>;
#[doc = "Field `FORCE_HP_MEM_ISO` reader - need_des"]
pub type FORCE_HP_MEM_ISO_R = crate::FieldReader;
#[doc = "Field `FORCE_HP_MEM_ISO` writer - need_des"]
pub type FORCE_HP_MEM_ISO_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `FORCE_HP_MEM_PD` reader - need_des"]
pub type FORCE_HP_MEM_PD_R = crate::FieldReader;
#[doc = "Field `FORCE_HP_MEM_PD` writer - need_des"]
pub type FORCE_HP_MEM_PD_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `FORCE_HP_MEM_NO_ISO` reader - need_des"]
pub type FORCE_HP_MEM_NO_ISO_R = crate::FieldReader;
#[doc = "Field `FORCE_HP_MEM_NO_ISO` writer - need_des"]
pub type FORCE_HP_MEM_NO_ISO_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `FORCE_HP_MEM_PU` reader - need_des"]
pub type FORCE_HP_MEM_PU_R = crate::FieldReader;
#[doc = "Field `FORCE_HP_MEM_PU` writer - need_des"]
pub type FORCE_HP_MEM_PU_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3 - need_des"]
    #[inline(always)]
    pub fn force_hp_mem_iso(&self) -> FORCE_HP_MEM_ISO_R {
        FORCE_HP_MEM_ISO_R::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:7 - need_des"]
    #[inline(always)]
    pub fn force_hp_mem_pd(&self) -> FORCE_HP_MEM_PD_R {
        FORCE_HP_MEM_PD_R::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bits 24:27 - need_des"]
    #[inline(always)]
    pub fn force_hp_mem_no_iso(&self) -> FORCE_HP_MEM_NO_ISO_R {
        FORCE_HP_MEM_NO_ISO_R::new(((self.bits >> 24) & 0x0f) as u8)
    }
    #[doc = "Bits 28:31 - need_des"]
    #[inline(always)]
    pub fn force_hp_mem_pu(&self) -> FORCE_HP_MEM_PU_R {
        FORCE_HP_MEM_PU_R::new(((self.bits >> 28) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("POWER_PD_MEM_CNTL")
            .field("force_hp_mem_iso", &self.force_hp_mem_iso())
            .field("force_hp_mem_pd", &self.force_hp_mem_pd())
            .field("force_hp_mem_no_iso", &self.force_hp_mem_no_iso())
            .field("force_hp_mem_pu", &self.force_hp_mem_pu())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3 - need_des"]
    #[inline(always)]
    pub fn force_hp_mem_iso(&mut self) -> FORCE_HP_MEM_ISO_W<'_, POWER_PD_MEM_CNTL_SPEC> {
        FORCE_HP_MEM_ISO_W::new(self, 0)
    }
    #[doc = "Bits 4:7 - need_des"]
    #[inline(always)]
    pub fn force_hp_mem_pd(&mut self) -> FORCE_HP_MEM_PD_W<'_, POWER_PD_MEM_CNTL_SPEC> {
        FORCE_HP_MEM_PD_W::new(self, 4)
    }
    #[doc = "Bits 24:27 - need_des"]
    #[inline(always)]
    pub fn force_hp_mem_no_iso(&mut self) -> FORCE_HP_MEM_NO_ISO_W<'_, POWER_PD_MEM_CNTL_SPEC> {
        FORCE_HP_MEM_NO_ISO_W::new(self, 24)
    }
    #[doc = "Bits 28:31 - need_des"]
    #[inline(always)]
    pub fn force_hp_mem_pu(&mut self) -> FORCE_HP_MEM_PU_W<'_, POWER_PD_MEM_CNTL_SPEC> {
        FORCE_HP_MEM_PU_W::new(self, 28)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`power_pd_mem_cntl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`power_pd_mem_cntl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct POWER_PD_MEM_CNTL_SPEC;
impl crate::RegisterSpec for POWER_PD_MEM_CNTL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`power_pd_mem_cntl::R`](R) reader structure"]
impl crate::Readable for POWER_PD_MEM_CNTL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`power_pd_mem_cntl::W`](W) writer structure"]
impl crate::Writable for POWER_PD_MEM_CNTL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets POWER_PD_MEM_CNTL to value 0xff00_0000"]
impl crate::Resettable for POWER_PD_MEM_CNTL_SPEC {
    const RESET_VALUE: u32 = 0xff00_0000;
}
