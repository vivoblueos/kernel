#[doc = "Register `LP_CPU_PWR1` reader"]
pub type R = crate::R<LP_CPU_PWR1_SPEC>;
#[doc = "Register `LP_CPU_PWR1` writer"]
pub type W = crate::W<LP_CPU_PWR1_SPEC>;
#[doc = "Field `LP_CPU_WAKEUP_EN` reader - need_des"]
pub type LP_CPU_WAKEUP_EN_R = crate::FieldReader<u16>;
#[doc = "Field `LP_CPU_WAKEUP_EN` writer - need_des"]
pub type LP_CPU_WAKEUP_EN_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `LP_CPU_SLEEP_REQ` writer - need_des"]
pub type LP_CPU_SLEEP_REQ_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:15 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_wakeup_en(&self) -> LP_CPU_WAKEUP_EN_R {
        LP_CPU_WAKEUP_EN_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LP_CPU_PWR1")
            .field("lp_cpu_wakeup_en", &self.lp_cpu_wakeup_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_wakeup_en(&mut self) -> LP_CPU_WAKEUP_EN_W<'_, LP_CPU_PWR1_SPEC> {
        LP_CPU_WAKEUP_EN_W::new(self, 0)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_sleep_req(&mut self) -> LP_CPU_SLEEP_REQ_W<'_, LP_CPU_PWR1_SPEC> {
        LP_CPU_SLEEP_REQ_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`lp_cpu_pwr1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lp_cpu_pwr1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LP_CPU_PWR1_SPEC;
impl crate::RegisterSpec for LP_CPU_PWR1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lp_cpu_pwr1::R`](R) reader structure"]
impl crate::Readable for LP_CPU_PWR1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`lp_cpu_pwr1::W`](W) writer structure"]
impl crate::Writable for LP_CPU_PWR1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LP_CPU_PWR1 to value 0"]
impl crate::Resettable for LP_CPU_PWR1_SPEC {}
