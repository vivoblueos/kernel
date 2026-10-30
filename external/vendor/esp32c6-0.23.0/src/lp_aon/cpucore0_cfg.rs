#[doc = "Register `CPUCORE0_CFG` reader"]
pub type R = crate::R<CPUCORE0_CFG_SPEC>;
#[doc = "Register `CPUCORE0_CFG` writer"]
pub type W = crate::W<CPUCORE0_CFG_SPEC>;
#[doc = "Field `CPU_CORE0_SW_STALL` reader - need_des"]
pub type CPU_CORE0_SW_STALL_R = crate::FieldReader;
#[doc = "Field `CPU_CORE0_SW_STALL` writer - need_des"]
pub type CPU_CORE0_SW_STALL_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `CPU_CORE0_SW_RESET` writer - need_des"]
pub type CPU_CORE0_SW_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CPU_CORE0_OCD_HALT_ON_RESET` reader - need_des"]
pub type CPU_CORE0_OCD_HALT_ON_RESET_R = crate::BitReader;
#[doc = "Field `CPU_CORE0_OCD_HALT_ON_RESET` writer - need_des"]
pub type CPU_CORE0_OCD_HALT_ON_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CPU_CORE0_STAT_VECTOR_SEL` reader - need_des"]
pub type CPU_CORE0_STAT_VECTOR_SEL_R = crate::BitReader;
#[doc = "Field `CPU_CORE0_STAT_VECTOR_SEL` writer - need_des"]
pub type CPU_CORE0_STAT_VECTOR_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CPU_CORE0_DRESET_MASK` reader - need_des"]
pub type CPU_CORE0_DRESET_MASK_R = crate::BitReader;
#[doc = "Field `CPU_CORE0_DRESET_MASK` writer - need_des"]
pub type CPU_CORE0_DRESET_MASK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:7 - need_des"]
    #[inline(always)]
    pub fn cpu_core0_sw_stall(&self) -> CPU_CORE0_SW_STALL_R {
        CPU_CORE0_SW_STALL_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn cpu_core0_ocd_halt_on_reset(&self) -> CPU_CORE0_OCD_HALT_ON_RESET_R {
        CPU_CORE0_OCD_HALT_ON_RESET_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn cpu_core0_stat_vector_sel(&self) -> CPU_CORE0_STAT_VECTOR_SEL_R {
        CPU_CORE0_STAT_VECTOR_SEL_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn cpu_core0_dreset_mask(&self) -> CPU_CORE0_DRESET_MASK_R {
        CPU_CORE0_DRESET_MASK_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CPUCORE0_CFG")
            .field("cpu_core0_sw_stall", &self.cpu_core0_sw_stall())
            .field(
                "cpu_core0_ocd_halt_on_reset",
                &self.cpu_core0_ocd_halt_on_reset(),
            )
            .field(
                "cpu_core0_stat_vector_sel",
                &self.cpu_core0_stat_vector_sel(),
            )
            .field("cpu_core0_dreset_mask", &self.cpu_core0_dreset_mask())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - need_des"]
    #[inline(always)]
    pub fn cpu_core0_sw_stall(&mut self) -> CPU_CORE0_SW_STALL_W<'_, CPUCORE0_CFG_SPEC> {
        CPU_CORE0_SW_STALL_W::new(self, 0)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn cpu_core0_sw_reset(&mut self) -> CPU_CORE0_SW_RESET_W<'_, CPUCORE0_CFG_SPEC> {
        CPU_CORE0_SW_RESET_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn cpu_core0_ocd_halt_on_reset(
        &mut self,
    ) -> CPU_CORE0_OCD_HALT_ON_RESET_W<'_, CPUCORE0_CFG_SPEC> {
        CPU_CORE0_OCD_HALT_ON_RESET_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn cpu_core0_stat_vector_sel(
        &mut self,
    ) -> CPU_CORE0_STAT_VECTOR_SEL_W<'_, CPUCORE0_CFG_SPEC> {
        CPU_CORE0_STAT_VECTOR_SEL_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn cpu_core0_dreset_mask(&mut self) -> CPU_CORE0_DRESET_MASK_W<'_, CPUCORE0_CFG_SPEC> {
        CPU_CORE0_DRESET_MASK_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`cpucore0_cfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpucore0_cfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CPUCORE0_CFG_SPEC;
impl crate::RegisterSpec for CPUCORE0_CFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cpucore0_cfg::R`](R) reader structure"]
impl crate::Readable for CPUCORE0_CFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cpucore0_cfg::W`](W) writer structure"]
impl crate::Writable for CPUCORE0_CFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CPUCORE0_CFG to value 0x4000_0000"]
impl crate::Resettable for CPUCORE0_CFG_SPEC {
    const RESET_VALUE: u32 = 0x4000_0000;
}
