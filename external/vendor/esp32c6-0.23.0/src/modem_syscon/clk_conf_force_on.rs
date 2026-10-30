#[doc = "Register `CLK_CONF_FORCE_ON` reader"]
pub type R = crate::R<CLK_CONF_FORCE_ON_SPEC>;
#[doc = "Register `CLK_CONF_FORCE_ON` writer"]
pub type W = crate::W<CLK_CONF_FORCE_ON_SPEC>;
#[doc = "Field `CLK_ETM_FO` reader - "]
pub type CLK_ETM_FO_R = crate::BitReader;
#[doc = "Field `CLK_ETM_FO` writer - "]
pub type CLK_ETM_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_ZB_APB_FO` reader - "]
pub type CLK_ZB_APB_FO_R = crate::BitReader;
#[doc = "Field `CLK_ZB_APB_FO` writer - "]
pub type CLK_ZB_APB_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_ZB_MAC_FO` reader - "]
pub type CLK_ZB_MAC_FO_R = crate::BitReader;
#[doc = "Field `CLK_ZB_MAC_FO` writer - "]
pub type CLK_ZB_MAC_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_MODEM_SEC_ECB_FO` reader - "]
pub type CLK_MODEM_SEC_ECB_FO_R = crate::BitReader;
#[doc = "Field `CLK_MODEM_SEC_ECB_FO` writer - "]
pub type CLK_MODEM_SEC_ECB_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_MODEM_SEC_CCM_FO` reader - "]
pub type CLK_MODEM_SEC_CCM_FO_R = crate::BitReader;
#[doc = "Field `CLK_MODEM_SEC_CCM_FO` writer - "]
pub type CLK_MODEM_SEC_CCM_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_MODEM_SEC_BAH_FO` reader - "]
pub type CLK_MODEM_SEC_BAH_FO_R = crate::BitReader;
#[doc = "Field `CLK_MODEM_SEC_BAH_FO` writer - "]
pub type CLK_MODEM_SEC_BAH_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_MODEM_SEC_APB_FO` reader - "]
pub type CLK_MODEM_SEC_APB_FO_R = crate::BitReader;
#[doc = "Field `CLK_MODEM_SEC_APB_FO` writer - "]
pub type CLK_MODEM_SEC_APB_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_MODEM_SEC_FO` reader - "]
pub type CLK_MODEM_SEC_FO_R = crate::BitReader;
#[doc = "Field `CLK_MODEM_SEC_FO` writer - "]
pub type CLK_MODEM_SEC_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_BLE_TIMER_FO` reader - "]
pub type CLK_BLE_TIMER_FO_R = crate::BitReader;
#[doc = "Field `CLK_BLE_TIMER_FO` writer - "]
pub type CLK_BLE_TIMER_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_DATA_DUMP_FO` reader - "]
pub type CLK_DATA_DUMP_FO_R = crate::BitReader;
#[doc = "Field `CLK_DATA_DUMP_FO` writer - "]
pub type CLK_DATA_DUMP_FO_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 22"]
    #[inline(always)]
    pub fn clk_etm_fo(&self) -> CLK_ETM_FO_R {
        CLK_ETM_FO_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23"]
    #[inline(always)]
    pub fn clk_zb_apb_fo(&self) -> CLK_ZB_APB_FO_R {
        CLK_ZB_APB_FO_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24"]
    #[inline(always)]
    pub fn clk_zb_mac_fo(&self) -> CLK_ZB_MAC_FO_R {
        CLK_ZB_MAC_FO_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25"]
    #[inline(always)]
    pub fn clk_modem_sec_ecb_fo(&self) -> CLK_MODEM_SEC_ECB_FO_R {
        CLK_MODEM_SEC_ECB_FO_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26"]
    #[inline(always)]
    pub fn clk_modem_sec_ccm_fo(&self) -> CLK_MODEM_SEC_CCM_FO_R {
        CLK_MODEM_SEC_CCM_FO_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27"]
    #[inline(always)]
    pub fn clk_modem_sec_bah_fo(&self) -> CLK_MODEM_SEC_BAH_FO_R {
        CLK_MODEM_SEC_BAH_FO_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28"]
    #[inline(always)]
    pub fn clk_modem_sec_apb_fo(&self) -> CLK_MODEM_SEC_APB_FO_R {
        CLK_MODEM_SEC_APB_FO_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29"]
    #[inline(always)]
    pub fn clk_modem_sec_fo(&self) -> CLK_MODEM_SEC_FO_R {
        CLK_MODEM_SEC_FO_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30"]
    #[inline(always)]
    pub fn clk_ble_timer_fo(&self) -> CLK_BLE_TIMER_FO_R {
        CLK_BLE_TIMER_FO_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31"]
    #[inline(always)]
    pub fn clk_data_dump_fo(&self) -> CLK_DATA_DUMP_FO_R {
        CLK_DATA_DUMP_FO_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLK_CONF_FORCE_ON")
            .field("clk_etm_fo", &self.clk_etm_fo())
            .field("clk_zb_apb_fo", &self.clk_zb_apb_fo())
            .field("clk_zb_mac_fo", &self.clk_zb_mac_fo())
            .field("clk_modem_sec_ecb_fo", &self.clk_modem_sec_ecb_fo())
            .field("clk_modem_sec_ccm_fo", &self.clk_modem_sec_ccm_fo())
            .field("clk_modem_sec_bah_fo", &self.clk_modem_sec_bah_fo())
            .field("clk_modem_sec_apb_fo", &self.clk_modem_sec_apb_fo())
            .field("clk_modem_sec_fo", &self.clk_modem_sec_fo())
            .field("clk_ble_timer_fo", &self.clk_ble_timer_fo())
            .field("clk_data_dump_fo", &self.clk_data_dump_fo())
            .finish()
    }
}
impl W {
    #[doc = "Bit 22"]
    #[inline(always)]
    pub fn clk_etm_fo(&mut self) -> CLK_ETM_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_ETM_FO_W::new(self, 22)
    }
    #[doc = "Bit 23"]
    #[inline(always)]
    pub fn clk_zb_apb_fo(&mut self) -> CLK_ZB_APB_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_ZB_APB_FO_W::new(self, 23)
    }
    #[doc = "Bit 24"]
    #[inline(always)]
    pub fn clk_zb_mac_fo(&mut self) -> CLK_ZB_MAC_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_ZB_MAC_FO_W::new(self, 24)
    }
    #[doc = "Bit 25"]
    #[inline(always)]
    pub fn clk_modem_sec_ecb_fo(&mut self) -> CLK_MODEM_SEC_ECB_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_MODEM_SEC_ECB_FO_W::new(self, 25)
    }
    #[doc = "Bit 26"]
    #[inline(always)]
    pub fn clk_modem_sec_ccm_fo(&mut self) -> CLK_MODEM_SEC_CCM_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_MODEM_SEC_CCM_FO_W::new(self, 26)
    }
    #[doc = "Bit 27"]
    #[inline(always)]
    pub fn clk_modem_sec_bah_fo(&mut self) -> CLK_MODEM_SEC_BAH_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_MODEM_SEC_BAH_FO_W::new(self, 27)
    }
    #[doc = "Bit 28"]
    #[inline(always)]
    pub fn clk_modem_sec_apb_fo(&mut self) -> CLK_MODEM_SEC_APB_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_MODEM_SEC_APB_FO_W::new(self, 28)
    }
    #[doc = "Bit 29"]
    #[inline(always)]
    pub fn clk_modem_sec_fo(&mut self) -> CLK_MODEM_SEC_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_MODEM_SEC_FO_W::new(self, 29)
    }
    #[doc = "Bit 30"]
    #[inline(always)]
    pub fn clk_ble_timer_fo(&mut self) -> CLK_BLE_TIMER_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_BLE_TIMER_FO_W::new(self, 30)
    }
    #[doc = "Bit 31"]
    #[inline(always)]
    pub fn clk_data_dump_fo(&mut self) -> CLK_DATA_DUMP_FO_W<'_, CLK_CONF_FORCE_ON_SPEC> {
        CLK_DATA_DUMP_FO_W::new(self, 31)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_conf_force_on::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_conf_force_on::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLK_CONF_FORCE_ON_SPEC;
impl crate::RegisterSpec for CLK_CONF_FORCE_ON_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clk_conf_force_on::R`](R) reader structure"]
impl crate::Readable for CLK_CONF_FORCE_ON_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clk_conf_force_on::W`](W) writer structure"]
impl crate::Writable for CLK_CONF_FORCE_ON_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLK_CONF_FORCE_ON to value 0"]
impl crate::Resettable for CLK_CONF_FORCE_ON_SPEC {}
