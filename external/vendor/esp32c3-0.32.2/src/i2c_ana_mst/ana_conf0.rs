#[doc = "Register `ANA_CONF0` reader"]
pub type R = crate::R<ANA_CONF0_SPEC>;
#[doc = "Register `ANA_CONF0` writer"]
pub type W = crate::W<ANA_CONF0_SPEC>;
#[doc = "Field `BBPLL_STOP_FORCE_HIGH` reader - ?"]
pub type BBPLL_STOP_FORCE_HIGH_R = crate::BitReader;
#[doc = "Field `BBPLL_STOP_FORCE_HIGH` writer - ?"]
pub type BBPLL_STOP_FORCE_HIGH_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BBPLL_STOP_FORCE_LOW` reader - ?"]
pub type BBPLL_STOP_FORCE_LOW_R = crate::BitReader;
#[doc = "Field `BBPLL_STOP_FORCE_LOW` writer - ?"]
pub type BBPLL_STOP_FORCE_LOW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BBPLL_CAL_DONE` reader - ?"]
pub type BBPLL_CAL_DONE_R = crate::BitReader;
#[doc = "Field `BBPLL_CAL_DONE` writer - ?"]
pub type BBPLL_CAL_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 2 - ?"]
    #[inline(always)]
    pub fn bbpll_stop_force_high(&self) -> BBPLL_STOP_FORCE_HIGH_R {
        BBPLL_STOP_FORCE_HIGH_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - ?"]
    #[inline(always)]
    pub fn bbpll_stop_force_low(&self) -> BBPLL_STOP_FORCE_LOW_R {
        BBPLL_STOP_FORCE_LOW_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 24 - ?"]
    #[inline(always)]
    pub fn bbpll_cal_done(&self) -> BBPLL_CAL_DONE_R {
        BBPLL_CAL_DONE_R::new(((self.bits >> 24) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ANA_CONF0")
            .field("bbpll_stop_force_high", &self.bbpll_stop_force_high())
            .field("bbpll_stop_force_low", &self.bbpll_stop_force_low())
            .field("bbpll_cal_done", &self.bbpll_cal_done())
            .finish()
    }
}
impl W {
    #[doc = "Bit 2 - ?"]
    #[inline(always)]
    pub fn bbpll_stop_force_high(&mut self) -> BBPLL_STOP_FORCE_HIGH_W<'_, ANA_CONF0_SPEC> {
        BBPLL_STOP_FORCE_HIGH_W::new(self, 2)
    }
    #[doc = "Bit 3 - ?"]
    #[inline(always)]
    pub fn bbpll_stop_force_low(&mut self) -> BBPLL_STOP_FORCE_LOW_W<'_, ANA_CONF0_SPEC> {
        BBPLL_STOP_FORCE_LOW_W::new(self, 3)
    }
    #[doc = "Bit 24 - ?"]
    #[inline(always)]
    pub fn bbpll_cal_done(&mut self) -> BBPLL_CAL_DONE_W<'_, ANA_CONF0_SPEC> {
        BBPLL_CAL_DONE_W::new(self, 24)
    }
}
#[doc = "ANA_CONF0 register\n\nYou can [`read`](crate::Reg::read) this register and get [`ana_conf0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ana_conf0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ANA_CONF0_SPEC;
impl crate::RegisterSpec for ANA_CONF0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ana_conf0::R`](R) reader structure"]
impl crate::Readable for ANA_CONF0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ana_conf0::W`](W) writer structure"]
impl crate::Writable for ANA_CONF0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ANA_CONF0 to value 0"]
impl crate::Resettable for ANA_CONF0_SPEC {}
