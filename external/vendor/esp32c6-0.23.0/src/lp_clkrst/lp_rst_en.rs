#[doc = "Register `LP_RST_EN` reader"]
pub type R = crate::R<LP_RST_EN_SPEC>;
#[doc = "Register `LP_RST_EN` writer"]
pub type W = crate::W<LP_RST_EN_SPEC>;
#[doc = "Field `AON_EFUSE_CORE_RESET_EN` reader - need_des"]
pub type AON_EFUSE_CORE_RESET_EN_R = crate::BitReader;
#[doc = "Field `AON_EFUSE_CORE_RESET_EN` writer - need_des"]
pub type AON_EFUSE_CORE_RESET_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LP_TIMER_RESET_EN` reader - need_des"]
pub type LP_TIMER_RESET_EN_R = crate::BitReader;
#[doc = "Field `LP_TIMER_RESET_EN` writer - need_des"]
pub type LP_TIMER_RESET_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WDT_RESET_EN` reader - need_des"]
pub type WDT_RESET_EN_R = crate::BitReader;
#[doc = "Field `WDT_RESET_EN` writer - need_des"]
pub type WDT_RESET_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ANA_PERI_RESET_EN` reader - need_des"]
pub type ANA_PERI_RESET_EN_R = crate::BitReader;
#[doc = "Field `ANA_PERI_RESET_EN` writer - need_des"]
pub type ANA_PERI_RESET_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn aon_efuse_core_reset_en(&self) -> AON_EFUSE_CORE_RESET_EN_R {
        AON_EFUSE_CORE_RESET_EN_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn lp_timer_reset_en(&self) -> LP_TIMER_RESET_EN_R {
        LP_TIMER_RESET_EN_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn wdt_reset_en(&self) -> WDT_RESET_EN_R {
        WDT_RESET_EN_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn ana_peri_reset_en(&self) -> ANA_PERI_RESET_EN_R {
        ANA_PERI_RESET_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LP_RST_EN")
            .field("aon_efuse_core_reset_en", &self.aon_efuse_core_reset_en())
            .field("lp_timer_reset_en", &self.lp_timer_reset_en())
            .field("wdt_reset_en", &self.wdt_reset_en())
            .field("ana_peri_reset_en", &self.ana_peri_reset_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn aon_efuse_core_reset_en(&mut self) -> AON_EFUSE_CORE_RESET_EN_W<'_, LP_RST_EN_SPEC> {
        AON_EFUSE_CORE_RESET_EN_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn lp_timer_reset_en(&mut self) -> LP_TIMER_RESET_EN_W<'_, LP_RST_EN_SPEC> {
        LP_TIMER_RESET_EN_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn wdt_reset_en(&mut self) -> WDT_RESET_EN_W<'_, LP_RST_EN_SPEC> {
        WDT_RESET_EN_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn ana_peri_reset_en(&mut self) -> ANA_PERI_RESET_EN_W<'_, LP_RST_EN_SPEC> {
        ANA_PERI_RESET_EN_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`lp_rst_en::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lp_rst_en::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LP_RST_EN_SPEC;
impl crate::RegisterSpec for LP_RST_EN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lp_rst_en::R`](R) reader structure"]
impl crate::Readable for LP_RST_EN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`lp_rst_en::W`](W) writer structure"]
impl crate::Writable for LP_RST_EN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LP_RST_EN to value 0"]
impl crate::Resettable for LP_RST_EN_SPEC {}
