#[doc = "Register `MODEM_RST_CONF` reader"]
pub type R = crate::R<MODEM_RST_CONF_SPEC>;
#[doc = "Register `MODEM_RST_CONF` writer"]
pub type W = crate::W<MODEM_RST_CONF_SPEC>;
#[doc = "Field `RST_WIFIBB` reader - "]
pub type RST_WIFIBB_R = crate::BitReader;
#[doc = "Field `RST_WIFIBB` writer - "]
pub type RST_WIFIBB_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_WIFIMAC` reader - "]
pub type RST_WIFIMAC_R = crate::BitReader;
#[doc = "Field `RST_WIFIMAC` writer - "]
pub type RST_WIFIMAC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_FE` reader - "]
pub type RST_FE_R = crate::BitReader;
#[doc = "Field `RST_FE` writer - "]
pub type RST_FE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_BTMAC_APB` reader - "]
pub type RST_BTMAC_APB_R = crate::BitReader;
#[doc = "Field `RST_BTMAC_APB` writer - "]
pub type RST_BTMAC_APB_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_BTMAC` reader - "]
pub type RST_BTMAC_R = crate::BitReader;
#[doc = "Field `RST_BTMAC` writer - "]
pub type RST_BTMAC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_BTBB_APB` reader - "]
pub type RST_BTBB_APB_R = crate::BitReader;
#[doc = "Field `RST_BTBB_APB` writer - "]
pub type RST_BTBB_APB_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_BTBB` reader - "]
pub type RST_BTBB_R = crate::BitReader;
#[doc = "Field `RST_BTBB` writer - "]
pub type RST_BTBB_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_ETM` reader - "]
pub type RST_ETM_R = crate::BitReader;
#[doc = "Field `RST_ETM` writer - "]
pub type RST_ETM_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_ZBMAC` reader - "]
pub type RST_ZBMAC_R = crate::BitReader;
#[doc = "Field `RST_ZBMAC` writer - "]
pub type RST_ZBMAC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_MODEM_ECB` reader - "]
pub type RST_MODEM_ECB_R = crate::BitReader;
#[doc = "Field `RST_MODEM_ECB` writer - "]
pub type RST_MODEM_ECB_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_MODEM_CCM` reader - "]
pub type RST_MODEM_CCM_R = crate::BitReader;
#[doc = "Field `RST_MODEM_CCM` writer - "]
pub type RST_MODEM_CCM_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_MODEM_BAH` reader - "]
pub type RST_MODEM_BAH_R = crate::BitReader;
#[doc = "Field `RST_MODEM_BAH` writer - "]
pub type RST_MODEM_BAH_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_MODEM_SEC` reader - "]
pub type RST_MODEM_SEC_R = crate::BitReader;
#[doc = "Field `RST_MODEM_SEC` writer - "]
pub type RST_MODEM_SEC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_BLE_TIMER` reader - "]
pub type RST_BLE_TIMER_R = crate::BitReader;
#[doc = "Field `RST_BLE_TIMER` writer - "]
pub type RST_BLE_TIMER_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST_DATA_DUMP` reader - "]
pub type RST_DATA_DUMP_R = crate::BitReader;
#[doc = "Field `RST_DATA_DUMP` writer - "]
pub type RST_DATA_DUMP_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 8"]
    #[inline(always)]
    pub fn rst_wifibb(&self) -> RST_WIFIBB_R {
        RST_WIFIBB_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 10"]
    #[inline(always)]
    pub fn rst_wifimac(&self) -> RST_WIFIMAC_R {
        RST_WIFIMAC_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 14"]
    #[inline(always)]
    pub fn rst_fe(&self) -> RST_FE_R {
        RST_FE_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15"]
    #[inline(always)]
    pub fn rst_btmac_apb(&self) -> RST_BTMAC_APB_R {
        RST_BTMAC_APB_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16"]
    #[inline(always)]
    pub fn rst_btmac(&self) -> RST_BTMAC_R {
        RST_BTMAC_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17"]
    #[inline(always)]
    pub fn rst_btbb_apb(&self) -> RST_BTBB_APB_R {
        RST_BTBB_APB_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18"]
    #[inline(always)]
    pub fn rst_btbb(&self) -> RST_BTBB_R {
        RST_BTBB_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 22"]
    #[inline(always)]
    pub fn rst_etm(&self) -> RST_ETM_R {
        RST_ETM_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 24"]
    #[inline(always)]
    pub fn rst_zbmac(&self) -> RST_ZBMAC_R {
        RST_ZBMAC_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25"]
    #[inline(always)]
    pub fn rst_modem_ecb(&self) -> RST_MODEM_ECB_R {
        RST_MODEM_ECB_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26"]
    #[inline(always)]
    pub fn rst_modem_ccm(&self) -> RST_MODEM_CCM_R {
        RST_MODEM_CCM_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27"]
    #[inline(always)]
    pub fn rst_modem_bah(&self) -> RST_MODEM_BAH_R {
        RST_MODEM_BAH_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 29"]
    #[inline(always)]
    pub fn rst_modem_sec(&self) -> RST_MODEM_SEC_R {
        RST_MODEM_SEC_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30"]
    #[inline(always)]
    pub fn rst_ble_timer(&self) -> RST_BLE_TIMER_R {
        RST_BLE_TIMER_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31"]
    #[inline(always)]
    pub fn rst_data_dump(&self) -> RST_DATA_DUMP_R {
        RST_DATA_DUMP_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MODEM_RST_CONF")
            .field("rst_wifibb", &self.rst_wifibb())
            .field("rst_wifimac", &self.rst_wifimac())
            .field("rst_fe", &self.rst_fe())
            .field("rst_btmac_apb", &self.rst_btmac_apb())
            .field("rst_btmac", &self.rst_btmac())
            .field("rst_btbb_apb", &self.rst_btbb_apb())
            .field("rst_btbb", &self.rst_btbb())
            .field("rst_etm", &self.rst_etm())
            .field("rst_zbmac", &self.rst_zbmac())
            .field("rst_modem_ecb", &self.rst_modem_ecb())
            .field("rst_modem_ccm", &self.rst_modem_ccm())
            .field("rst_modem_bah", &self.rst_modem_bah())
            .field("rst_modem_sec", &self.rst_modem_sec())
            .field("rst_ble_timer", &self.rst_ble_timer())
            .field("rst_data_dump", &self.rst_data_dump())
            .finish()
    }
}
impl W {
    #[doc = "Bit 8"]
    #[inline(always)]
    pub fn rst_wifibb(&mut self) -> RST_WIFIBB_W<'_, MODEM_RST_CONF_SPEC> {
        RST_WIFIBB_W::new(self, 8)
    }
    #[doc = "Bit 10"]
    #[inline(always)]
    pub fn rst_wifimac(&mut self) -> RST_WIFIMAC_W<'_, MODEM_RST_CONF_SPEC> {
        RST_WIFIMAC_W::new(self, 10)
    }
    #[doc = "Bit 14"]
    #[inline(always)]
    pub fn rst_fe(&mut self) -> RST_FE_W<'_, MODEM_RST_CONF_SPEC> {
        RST_FE_W::new(self, 14)
    }
    #[doc = "Bit 15"]
    #[inline(always)]
    pub fn rst_btmac_apb(&mut self) -> RST_BTMAC_APB_W<'_, MODEM_RST_CONF_SPEC> {
        RST_BTMAC_APB_W::new(self, 15)
    }
    #[doc = "Bit 16"]
    #[inline(always)]
    pub fn rst_btmac(&mut self) -> RST_BTMAC_W<'_, MODEM_RST_CONF_SPEC> {
        RST_BTMAC_W::new(self, 16)
    }
    #[doc = "Bit 17"]
    #[inline(always)]
    pub fn rst_btbb_apb(&mut self) -> RST_BTBB_APB_W<'_, MODEM_RST_CONF_SPEC> {
        RST_BTBB_APB_W::new(self, 17)
    }
    #[doc = "Bit 18"]
    #[inline(always)]
    pub fn rst_btbb(&mut self) -> RST_BTBB_W<'_, MODEM_RST_CONF_SPEC> {
        RST_BTBB_W::new(self, 18)
    }
    #[doc = "Bit 22"]
    #[inline(always)]
    pub fn rst_etm(&mut self) -> RST_ETM_W<'_, MODEM_RST_CONF_SPEC> {
        RST_ETM_W::new(self, 22)
    }
    #[doc = "Bit 24"]
    #[inline(always)]
    pub fn rst_zbmac(&mut self) -> RST_ZBMAC_W<'_, MODEM_RST_CONF_SPEC> {
        RST_ZBMAC_W::new(self, 24)
    }
    #[doc = "Bit 25"]
    #[inline(always)]
    pub fn rst_modem_ecb(&mut self) -> RST_MODEM_ECB_W<'_, MODEM_RST_CONF_SPEC> {
        RST_MODEM_ECB_W::new(self, 25)
    }
    #[doc = "Bit 26"]
    #[inline(always)]
    pub fn rst_modem_ccm(&mut self) -> RST_MODEM_CCM_W<'_, MODEM_RST_CONF_SPEC> {
        RST_MODEM_CCM_W::new(self, 26)
    }
    #[doc = "Bit 27"]
    #[inline(always)]
    pub fn rst_modem_bah(&mut self) -> RST_MODEM_BAH_W<'_, MODEM_RST_CONF_SPEC> {
        RST_MODEM_BAH_W::new(self, 27)
    }
    #[doc = "Bit 29"]
    #[inline(always)]
    pub fn rst_modem_sec(&mut self) -> RST_MODEM_SEC_W<'_, MODEM_RST_CONF_SPEC> {
        RST_MODEM_SEC_W::new(self, 29)
    }
    #[doc = "Bit 30"]
    #[inline(always)]
    pub fn rst_ble_timer(&mut self) -> RST_BLE_TIMER_W<'_, MODEM_RST_CONF_SPEC> {
        RST_BLE_TIMER_W::new(self, 30)
    }
    #[doc = "Bit 31"]
    #[inline(always)]
    pub fn rst_data_dump(&mut self) -> RST_DATA_DUMP_W<'_, MODEM_RST_CONF_SPEC> {
        RST_DATA_DUMP_W::new(self, 31)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`modem_rst_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`modem_rst_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MODEM_RST_CONF_SPEC;
impl crate::RegisterSpec for MODEM_RST_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`modem_rst_conf::R`](R) reader structure"]
impl crate::Readable for MODEM_RST_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`modem_rst_conf::W`](W) writer structure"]
impl crate::Writable for MODEM_RST_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MODEM_RST_CONF to value 0"]
impl crate::Resettable for MODEM_RST_CONF_SPEC {}
