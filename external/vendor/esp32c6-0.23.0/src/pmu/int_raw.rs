#[doc = "Register `INT_RAW` reader"]
pub type R = crate::R<INT_RAW_SPEC>;
#[doc = "Register `INT_RAW` writer"]
pub type W = crate::W<INT_RAW_SPEC>;
#[doc = "Field `LP_CPU_EXC` reader - need_des"]
pub type LP_CPU_EXC_R = crate::BitReader;
#[doc = "Field `LP_CPU_EXC` writer - need_des"]
pub type LP_CPU_EXC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_IDLE` reader - need_des"]
pub type SDIO_IDLE_R = crate::BitReader;
#[doc = "Field `SDIO_IDLE` writer - need_des"]
pub type SDIO_IDLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SW` reader - need_des"]
pub type SW_R = crate::BitReader;
#[doc = "Field `SW` writer - need_des"]
pub type SW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SOC_SLEEP_REJECT` reader - need_des"]
pub type SOC_SLEEP_REJECT_R = crate::BitReader;
#[doc = "Field `SOC_SLEEP_REJECT` writer - need_des"]
pub type SOC_SLEEP_REJECT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SOC_WAKEUP` reader - need_des"]
pub type SOC_WAKEUP_R = crate::BitReader;
#[doc = "Field `SOC_WAKEUP` writer - need_des"]
pub type SOC_WAKEUP_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_exc(&self) -> LP_CPU_EXC_R {
        LP_CPU_EXC_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn sdio_idle(&self) -> SDIO_IDLE_R {
        SDIO_IDLE_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn sw(&self) -> SW_R {
        SW_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn soc_sleep_reject(&self) -> SOC_SLEEP_REJECT_R {
        SOC_SLEEP_REJECT_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn soc_wakeup(&self) -> SOC_WAKEUP_R {
        SOC_WAKEUP_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_RAW")
            .field("lp_cpu_exc", &self.lp_cpu_exc())
            .field("sdio_idle", &self.sdio_idle())
            .field("sw", &self.sw())
            .field("soc_sleep_reject", &self.soc_sleep_reject())
            .field("soc_wakeup", &self.soc_wakeup())
            .finish()
    }
}
impl W {
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_exc(&mut self) -> LP_CPU_EXC_W<'_, INT_RAW_SPEC> {
        LP_CPU_EXC_W::new(self, 27)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn sdio_idle(&mut self) -> SDIO_IDLE_W<'_, INT_RAW_SPEC> {
        SDIO_IDLE_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn sw(&mut self) -> SW_W<'_, INT_RAW_SPEC> {
        SW_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn soc_sleep_reject(&mut self) -> SOC_SLEEP_REJECT_W<'_, INT_RAW_SPEC> {
        SOC_SLEEP_REJECT_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn soc_wakeup(&mut self) -> SOC_WAKEUP_W<'_, INT_RAW_SPEC> {
        SOC_WAKEUP_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_raw::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_RAW_SPEC;
impl crate::RegisterSpec for INT_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_raw::R`](R) reader structure"]
impl crate::Readable for INT_RAW_SPEC {}
#[doc = "`write(|w| ..)` method takes [`int_raw::W`](W) writer structure"]
impl crate::Writable for INT_RAW_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_RAW to value 0"]
impl crate::Resettable for INT_RAW_SPEC {}
