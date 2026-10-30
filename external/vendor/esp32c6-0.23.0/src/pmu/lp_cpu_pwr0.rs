#[doc = "Register `LP_CPU_PWR0` reader"]
pub type R = crate::R<LP_CPU_PWR0_SPEC>;
#[doc = "Register `LP_CPU_PWR0` writer"]
pub type W = crate::W<LP_CPU_PWR0_SPEC>;
#[doc = "Field `LP_CPU_WAITI_RDY` reader - need_des"]
pub type LP_CPU_WAITI_RDY_R = crate::BitReader;
#[doc = "Field `LP_CPU_STALL_RDY` reader - need_des"]
pub type LP_CPU_STALL_RDY_R = crate::BitReader;
#[doc = "Field `LP_CPU_FORCE_STALL` reader - need_des"]
pub type LP_CPU_FORCE_STALL_R = crate::BitReader;
#[doc = "Field `LP_CPU_FORCE_STALL` writer - need_des"]
pub type LP_CPU_FORCE_STALL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_CPU_SLP_WAITI_FLAG_EN` reader - need_des"]
pub type LP_CPU_SLP_WAITI_FLAG_EN_R = crate::BitReader;
#[doc = "Field `LP_CPU_SLP_WAITI_FLAG_EN` writer - need_des"]
pub type LP_CPU_SLP_WAITI_FLAG_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_CPU_SLP_STALL_FLAG_EN` reader - need_des"]
pub type LP_CPU_SLP_STALL_FLAG_EN_R = crate::BitReader;
#[doc = "Field `LP_CPU_SLP_STALL_FLAG_EN` writer - need_des"]
pub type LP_CPU_SLP_STALL_FLAG_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_CPU_SLP_STALL_WAIT` reader - need_des"]
pub type LP_CPU_SLP_STALL_WAIT_R = crate::FieldReader;
#[doc = "Field `LP_CPU_SLP_STALL_WAIT` writer - need_des"]
pub type LP_CPU_SLP_STALL_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `LP_CPU_SLP_STALL_EN` reader - need_des"]
pub type LP_CPU_SLP_STALL_EN_R = crate::BitReader;
#[doc = "Field `LP_CPU_SLP_STALL_EN` writer - need_des"]
pub type LP_CPU_SLP_STALL_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_CPU_SLP_RESET_EN` reader - need_des"]
pub type LP_CPU_SLP_RESET_EN_R = crate::BitReader;
#[doc = "Field `LP_CPU_SLP_RESET_EN` writer - need_des"]
pub type LP_CPU_SLP_RESET_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_CPU_SLP_BYPASS_INTR_EN` reader - need_des"]
pub type LP_CPU_SLP_BYPASS_INTR_EN_R = crate::BitReader;
#[doc = "Field `LP_CPU_SLP_BYPASS_INTR_EN` writer - need_des"]
pub type LP_CPU_SLP_BYPASS_INTR_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_waiti_rdy(&self) -> LP_CPU_WAITI_RDY_R {
        LP_CPU_WAITI_RDY_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_stall_rdy(&self) -> LP_CPU_STALL_RDY_R {
        LP_CPU_STALL_RDY_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 18 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_force_stall(&self) -> LP_CPU_FORCE_STALL_R {
        LP_CPU_FORCE_STALL_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_slp_waiti_flag_en(&self) -> LP_CPU_SLP_WAITI_FLAG_EN_R {
        LP_CPU_SLP_WAITI_FLAG_EN_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_slp_stall_flag_en(&self) -> LP_CPU_SLP_STALL_FLAG_EN_R {
        LP_CPU_SLP_STALL_FLAG_EN_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bits 21:28 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_slp_stall_wait(&self) -> LP_CPU_SLP_STALL_WAIT_R {
        LP_CPU_SLP_STALL_WAIT_R::new(((self.bits >> 21) & 0xff) as u8)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_slp_stall_en(&self) -> LP_CPU_SLP_STALL_EN_R {
        LP_CPU_SLP_STALL_EN_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_slp_reset_en(&self) -> LP_CPU_SLP_RESET_EN_R {
        LP_CPU_SLP_RESET_EN_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_slp_bypass_intr_en(&self) -> LP_CPU_SLP_BYPASS_INTR_EN_R {
        LP_CPU_SLP_BYPASS_INTR_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LP_CPU_PWR0")
            .field("lp_cpu_waiti_rdy", &self.lp_cpu_waiti_rdy())
            .field("lp_cpu_stall_rdy", &self.lp_cpu_stall_rdy())
            .field("lp_cpu_force_stall", &self.lp_cpu_force_stall())
            .field("lp_cpu_slp_waiti_flag_en", &self.lp_cpu_slp_waiti_flag_en())
            .field("lp_cpu_slp_stall_flag_en", &self.lp_cpu_slp_stall_flag_en())
            .field("lp_cpu_slp_stall_wait", &self.lp_cpu_slp_stall_wait())
            .field("lp_cpu_slp_stall_en", &self.lp_cpu_slp_stall_en())
            .field("lp_cpu_slp_reset_en", &self.lp_cpu_slp_reset_en())
            .field(
                "lp_cpu_slp_bypass_intr_en",
                &self.lp_cpu_slp_bypass_intr_en(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 18 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_force_stall(&mut self) -> LP_CPU_FORCE_STALL_W<'_, LP_CPU_PWR0_SPEC> {
        LP_CPU_FORCE_STALL_W::new(self, 18)
    }
    #[doc = "Bit 19 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_slp_waiti_flag_en(&mut self) -> LP_CPU_SLP_WAITI_FLAG_EN_W<'_, LP_CPU_PWR0_SPEC> {
        LP_CPU_SLP_WAITI_FLAG_EN_W::new(self, 19)
    }
    #[doc = "Bit 20 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_slp_stall_flag_en(&mut self) -> LP_CPU_SLP_STALL_FLAG_EN_W<'_, LP_CPU_PWR0_SPEC> {
        LP_CPU_SLP_STALL_FLAG_EN_W::new(self, 20)
    }
    #[doc = "Bits 21:28 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_slp_stall_wait(&mut self) -> LP_CPU_SLP_STALL_WAIT_W<'_, LP_CPU_PWR0_SPEC> {
        LP_CPU_SLP_STALL_WAIT_W::new(self, 21)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_slp_stall_en(&mut self) -> LP_CPU_SLP_STALL_EN_W<'_, LP_CPU_PWR0_SPEC> {
        LP_CPU_SLP_STALL_EN_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_slp_reset_en(&mut self) -> LP_CPU_SLP_RESET_EN_W<'_, LP_CPU_PWR0_SPEC> {
        LP_CPU_SLP_RESET_EN_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_slp_bypass_intr_en(
        &mut self,
    ) -> LP_CPU_SLP_BYPASS_INTR_EN_W<'_, LP_CPU_PWR0_SPEC> {
        LP_CPU_SLP_BYPASS_INTR_EN_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`lp_cpu_pwr0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lp_cpu_pwr0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LP_CPU_PWR0_SPEC;
impl crate::RegisterSpec for LP_CPU_PWR0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lp_cpu_pwr0::R`](R) reader structure"]
impl crate::Readable for LP_CPU_PWR0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`lp_cpu_pwr0::W`](W) writer structure"]
impl crate::Writable for LP_CPU_PWR0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LP_CPU_PWR0 to value 0x1ff0_0000"]
impl crate::Resettable for LP_CPU_PWR0_SPEC {
    const RESET_VALUE: u32 = 0x1ff0_0000;
}
