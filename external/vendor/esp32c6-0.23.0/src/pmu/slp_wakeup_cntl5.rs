#[doc = "Register `SLP_WAKEUP_CNTL5` reader"]
pub type R = crate::R<SLP_WAKEUP_CNTL5_SPEC>;
#[doc = "Register `SLP_WAKEUP_CNTL5` writer"]
pub type W = crate::W<SLP_WAKEUP_CNTL5_SPEC>;
#[doc = "Field `MODEM_WAIT_TARGET` reader - need_des"]
pub type MODEM_WAIT_TARGET_R = crate::FieldReader<u32>;
#[doc = "Field `MODEM_WAIT_TARGET` writer - need_des"]
pub type MODEM_WAIT_TARGET_W<'a, REG> = crate::FieldWriter<'a, REG, 20, u32>;
#[doc = "Field `LP_ANA_WAIT_TARGET` reader - need_des"]
pub type LP_ANA_WAIT_TARGET_R = crate::FieldReader;
#[doc = "Field `LP_ANA_WAIT_TARGET` writer - need_des"]
pub type LP_ANA_WAIT_TARGET_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:19 - need_des"]
    #[inline(always)]
    pub fn modem_wait_target(&self) -> MODEM_WAIT_TARGET_R {
        MODEM_WAIT_TARGET_R::new(self.bits & 0x000f_ffff)
    }
    #[doc = "Bits 24:31 - need_des"]
    #[inline(always)]
    pub fn lp_ana_wait_target(&self) -> LP_ANA_WAIT_TARGET_R {
        LP_ANA_WAIT_TARGET_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLP_WAKEUP_CNTL5")
            .field("modem_wait_target", &self.modem_wait_target())
            .field("lp_ana_wait_target", &self.lp_ana_wait_target())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:19 - need_des"]
    #[inline(always)]
    pub fn modem_wait_target(&mut self) -> MODEM_WAIT_TARGET_W<'_, SLP_WAKEUP_CNTL5_SPEC> {
        MODEM_WAIT_TARGET_W::new(self, 0)
    }
    #[doc = "Bits 24:31 - need_des"]
    #[inline(always)]
    pub fn lp_ana_wait_target(&mut self) -> LP_ANA_WAIT_TARGET_W<'_, SLP_WAKEUP_CNTL5_SPEC> {
        LP_ANA_WAIT_TARGET_W::new(self, 24)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`slp_wakeup_cntl5::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slp_wakeup_cntl5::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLP_WAKEUP_CNTL5_SPEC;
impl crate::RegisterSpec for SLP_WAKEUP_CNTL5_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slp_wakeup_cntl5::R`](R) reader structure"]
impl crate::Readable for SLP_WAKEUP_CNTL5_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slp_wakeup_cntl5::W`](W) writer structure"]
impl crate::Writable for SLP_WAKEUP_CNTL5_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLP_WAKEUP_CNTL5 to value 0x0100_0080"]
impl crate::Resettable for SLP_WAKEUP_CNTL5_SPEC {
    const RESET_VALUE: u32 = 0x0100_0080;
}
