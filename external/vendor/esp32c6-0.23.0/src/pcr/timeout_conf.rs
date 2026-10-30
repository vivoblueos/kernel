#[doc = "Register `TIMEOUT_CONF` reader"]
pub type R = crate::R<TIMEOUT_CONF_SPEC>;
#[doc = "Register `TIMEOUT_CONF` writer"]
pub type W = crate::W<TIMEOUT_CONF_SPEC>;
#[doc = "Field `CPU_TIMEOUT_RST_EN` reader - Set 0 to reset cpu_peri timeout module"]
pub type CPU_TIMEOUT_RST_EN_R = crate::BitReader;
#[doc = "Field `CPU_TIMEOUT_RST_EN` writer - Set 0 to reset cpu_peri timeout module"]
pub type CPU_TIMEOUT_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_TIMEOUT_RST_EN` reader - Set 0 to reset hp_peri timeout module and hp_modem timeout module"]
pub type HP_TIMEOUT_RST_EN_R = crate::BitReader;
#[doc = "Field `HP_TIMEOUT_RST_EN` writer - Set 0 to reset hp_peri timeout module and hp_modem timeout module"]
pub type HP_TIMEOUT_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 1 - Set 0 to reset cpu_peri timeout module"]
    #[inline(always)]
    pub fn cpu_timeout_rst_en(&self) -> CPU_TIMEOUT_RST_EN_R {
        CPU_TIMEOUT_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set 0 to reset hp_peri timeout module and hp_modem timeout module"]
    #[inline(always)]
    pub fn hp_timeout_rst_en(&self) -> HP_TIMEOUT_RST_EN_R {
        HP_TIMEOUT_RST_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TIMEOUT_CONF")
            .field("cpu_timeout_rst_en", &self.cpu_timeout_rst_en())
            .field("hp_timeout_rst_en", &self.hp_timeout_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 1 - Set 0 to reset cpu_peri timeout module"]
    #[inline(always)]
    pub fn cpu_timeout_rst_en(&mut self) -> CPU_TIMEOUT_RST_EN_W<'_, TIMEOUT_CONF_SPEC> {
        CPU_TIMEOUT_RST_EN_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set 0 to reset hp_peri timeout module and hp_modem timeout module"]
    #[inline(always)]
    pub fn hp_timeout_rst_en(&mut self) -> HP_TIMEOUT_RST_EN_W<'_, TIMEOUT_CONF_SPEC> {
        HP_TIMEOUT_RST_EN_W::new(self, 2)
    }
}
#[doc = "TIMEOUT configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`timeout_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`timeout_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TIMEOUT_CONF_SPEC;
impl crate::RegisterSpec for TIMEOUT_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`timeout_conf::R`](R) reader structure"]
impl crate::Readable for TIMEOUT_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`timeout_conf::W`](W) writer structure"]
impl crate::Writable for TIMEOUT_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TIMEOUT_CONF to value 0"]
impl crate::Resettable for TIMEOUT_CONF_SPEC {}
