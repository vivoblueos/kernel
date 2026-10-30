#[doc = "Register `WIFI_BB_CFG_2` reader"]
pub type R = crate::R<WIFI_BB_CFG_2_SPEC>;
#[doc = "Register `WIFI_BB_CFG_2` writer"]
pub type W = crate::W<WIFI_BB_CFG_2_SPEC>;
#[doc = "Field `WIFI_BB_CFG_2` reader - reg_wifi_bb_cfg_2"]
pub type WIFI_BB_CFG_2_R = crate::FieldReader<u32>;
#[doc = "Field `WIFI_BB_CFG_2` writer - reg_wifi_bb_cfg_2"]
pub type WIFI_BB_CFG_2_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - reg_wifi_bb_cfg_2"]
    #[inline(always)]
    pub fn wifi_bb_cfg_2(&self) -> WIFI_BB_CFG_2_R {
        WIFI_BB_CFG_2_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("WIFI_BB_CFG_2")
            .field("wifi_bb_cfg_2", &self.wifi_bb_cfg_2())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - reg_wifi_bb_cfg_2"]
    #[inline(always)]
    pub fn wifi_bb_cfg_2(&mut self) -> WIFI_BB_CFG_2_W<'_, WIFI_BB_CFG_2_SPEC> {
        WIFI_BB_CFG_2_W::new(self, 0)
    }
}
#[doc = "APB_CTRL_WIFI_BB_CFG_2_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`wifi_bb_cfg_2::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wifi_bb_cfg_2::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct WIFI_BB_CFG_2_SPEC;
impl crate::RegisterSpec for WIFI_BB_CFG_2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`wifi_bb_cfg_2::R`](R) reader structure"]
impl crate::Readable for WIFI_BB_CFG_2_SPEC {}
#[doc = "`write(|w| ..)` method takes [`wifi_bb_cfg_2::W`](W) writer structure"]
impl crate::Writable for WIFI_BB_CFG_2_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets WIFI_BB_CFG_2 to value 0"]
impl crate::Resettable for WIFI_BB_CFG_2_SPEC {}
