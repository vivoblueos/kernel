#[doc = "Register `CTRL_CFG` reader"]
pub type R = crate::R<CTRL_CFG_SPEC>;
#[doc = "Register `CTRL_CFG` writer"]
pub type W = crate::W<CTRL_CFG_SPEC>;
#[doc = "Field `HW_AUTO_ACK_TX_EN` reader - "]
pub type HW_AUTO_ACK_TX_EN_R = crate::BitReader;
#[doc = "Field `HW_AUTO_ACK_TX_EN` writer - "]
pub type HW_AUTO_ACK_TX_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HW_ENHANCE_ACK_TX_EN` reader - "]
pub type HW_ENHANCE_ACK_TX_EN_R = crate::BitReader;
#[doc = "Field `HW_ENHANCE_ACK_TX_EN` writer - "]
pub type HW_ENHANCE_ACK_TX_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HW_AUTO_ACK_RX_EN` reader - "]
pub type HW_AUTO_ACK_RX_EN_R = crate::BitReader;
#[doc = "Field `HW_AUTO_ACK_RX_EN` writer - "]
pub type HW_AUTO_ACK_RX_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DIS_IFS_CONTROL` reader - "]
pub type DIS_IFS_CONTROL_R = crate::BitReader;
#[doc = "Field `DIS_IFS_CONTROL` writer - "]
pub type DIS_IFS_CONTROL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PAN_COORDINATOR` reader - "]
pub type PAN_COORDINATOR_R = crate::BitReader;
#[doc = "Field `PAN_COORDINATOR` writer - "]
pub type PAN_COORDINATOR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PROMISCUOUS_MODE` reader - "]
pub type PROMISCUOUS_MODE_R = crate::BitReader;
#[doc = "Field `PROMISCUOUS_MODE` writer - "]
pub type PROMISCUOUS_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DIS_FRAME_VERSION_RSV_FILTER` reader - "]
pub type DIS_FRAME_VERSION_RSV_FILTER_R = crate::BitReader;
#[doc = "Field `DIS_FRAME_VERSION_RSV_FILTER` writer - "]
pub type DIS_FRAME_VERSION_RSV_FILTER_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AUTOPEND_ENHANCE` reader - "]
pub type AUTOPEND_ENHANCE_R = crate::BitReader;
#[doc = "Field `AUTOPEND_ENHANCE` writer - "]
pub type AUTOPEND_ENHANCE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FILTER_ENHANCE` reader - "]
pub type FILTER_ENHANCE_R = crate::BitReader;
#[doc = "Field `FILTER_ENHANCE` writer - "]
pub type FILTER_ENHANCE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `COEX_ARB_DELAY` reader - "]
pub type COEX_ARB_DELAY_R = crate::FieldReader;
#[doc = "Field `COEX_ARB_DELAY` writer - "]
pub type COEX_ARB_DELAY_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `BIT_ORDER` reader - "]
pub type BIT_ORDER_R = crate::BitReader;
#[doc = "Field `BIT_ORDER` writer - "]
pub type BIT_ORDER_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NO_RSS_TRK_ENB` reader - "]
pub type NO_RSS_TRK_ENB_R = crate::BitReader;
#[doc = "Field `NO_RSS_TRK_ENB` writer - "]
pub type NO_RSS_TRK_ENB_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FORCE_RX_ENB` reader - "]
pub type FORCE_RX_ENB_R = crate::BitReader;
#[doc = "Field `FORCE_RX_ENB` writer - "]
pub type FORCE_RX_ENB_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_DONE_TRIGGER_IDLE` reader - "]
pub type RX_DONE_TRIGGER_IDLE_R = crate::BitReader;
#[doc = "Field `RX_DONE_TRIGGER_IDLE` writer - "]
pub type RX_DONE_TRIGGER_IDLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MAC_INF0_ENABLE` reader - "]
pub type MAC_INF0_ENABLE_R = crate::BitReader;
#[doc = "Field `MAC_INF0_ENABLE` writer - "]
pub type MAC_INF0_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MAC_INF1_ENABLE` reader - "]
pub type MAC_INF1_ENABLE_R = crate::BitReader;
#[doc = "Field `MAC_INF1_ENABLE` writer - "]
pub type MAC_INF1_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MAC_INF2_ENABLE` reader - "]
pub type MAC_INF2_ENABLE_R = crate::BitReader;
#[doc = "Field `MAC_INF2_ENABLE` writer - "]
pub type MAC_INF2_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MAC_INF3_ENABLE` reader - "]
pub type MAC_INF3_ENABLE_R = crate::BitReader;
#[doc = "Field `MAC_INF3_ENABLE` writer - "]
pub type MAC_INF3_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn hw_auto_ack_tx_en(&self) -> HW_AUTO_ACK_TX_EN_R {
        HW_AUTO_ACK_TX_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn hw_enhance_ack_tx_en(&self) -> HW_ENHANCE_ACK_TX_EN_R {
        HW_ENHANCE_ACK_TX_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn hw_auto_ack_rx_en(&self) -> HW_AUTO_ACK_RX_EN_R {
        HW_AUTO_ACK_RX_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 5"]
    #[inline(always)]
    pub fn dis_ifs_control(&self) -> DIS_IFS_CONTROL_R {
        DIS_IFS_CONTROL_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6"]
    #[inline(always)]
    pub fn pan_coordinator(&self) -> PAN_COORDINATOR_R {
        PAN_COORDINATOR_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7"]
    #[inline(always)]
    pub fn promiscuous_mode(&self) -> PROMISCUOUS_MODE_R {
        PROMISCUOUS_MODE_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 11"]
    #[inline(always)]
    pub fn dis_frame_version_rsv_filter(&self) -> DIS_FRAME_VERSION_RSV_FILTER_R {
        DIS_FRAME_VERSION_RSV_FILTER_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12"]
    #[inline(always)]
    pub fn autopend_enhance(&self) -> AUTOPEND_ENHANCE_R {
        AUTOPEND_ENHANCE_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 14"]
    #[inline(always)]
    pub fn filter_enhance(&self) -> FILTER_ENHANCE_R {
        FILTER_ENHANCE_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bits 16:20"]
    #[inline(always)]
    pub fn coex_arb_delay(&self) -> COEX_ARB_DELAY_R {
        COEX_ARB_DELAY_R::new(((self.bits >> 16) & 0x1f) as u8)
    }
    #[doc = "Bit 24"]
    #[inline(always)]
    pub fn bit_order(&self) -> BIT_ORDER_R {
        BIT_ORDER_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25"]
    #[inline(always)]
    pub fn no_rss_trk_enb(&self) -> NO_RSS_TRK_ENB_R {
        NO_RSS_TRK_ENB_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26"]
    #[inline(always)]
    pub fn force_rx_enb(&self) -> FORCE_RX_ENB_R {
        FORCE_RX_ENB_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27"]
    #[inline(always)]
    pub fn rx_done_trigger_idle(&self) -> RX_DONE_TRIGGER_IDLE_R {
        RX_DONE_TRIGGER_IDLE_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28"]
    #[inline(always)]
    pub fn mac_inf0_enable(&self) -> MAC_INF0_ENABLE_R {
        MAC_INF0_ENABLE_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29"]
    #[inline(always)]
    pub fn mac_inf1_enable(&self) -> MAC_INF1_ENABLE_R {
        MAC_INF1_ENABLE_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30"]
    #[inline(always)]
    pub fn mac_inf2_enable(&self) -> MAC_INF2_ENABLE_R {
        MAC_INF2_ENABLE_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31"]
    #[inline(always)]
    pub fn mac_inf3_enable(&self) -> MAC_INF3_ENABLE_R {
        MAC_INF3_ENABLE_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CTRL_CFG")
            .field("hw_auto_ack_tx_en", &self.hw_auto_ack_tx_en())
            .field("hw_enhance_ack_tx_en", &self.hw_enhance_ack_tx_en())
            .field("hw_auto_ack_rx_en", &self.hw_auto_ack_rx_en())
            .field("dis_ifs_control", &self.dis_ifs_control())
            .field("pan_coordinator", &self.pan_coordinator())
            .field("promiscuous_mode", &self.promiscuous_mode())
            .field(
                "dis_frame_version_rsv_filter",
                &self.dis_frame_version_rsv_filter(),
            )
            .field("autopend_enhance", &self.autopend_enhance())
            .field("filter_enhance", &self.filter_enhance())
            .field("coex_arb_delay", &self.coex_arb_delay())
            .field("bit_order", &self.bit_order())
            .field("no_rss_trk_enb", &self.no_rss_trk_enb())
            .field("force_rx_enb", &self.force_rx_enb())
            .field("rx_done_trigger_idle", &self.rx_done_trigger_idle())
            .field("mac_inf0_enable", &self.mac_inf0_enable())
            .field("mac_inf1_enable", &self.mac_inf1_enable())
            .field("mac_inf2_enable", &self.mac_inf2_enable())
            .field("mac_inf3_enable", &self.mac_inf3_enable())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn hw_auto_ack_tx_en(&mut self) -> HW_AUTO_ACK_TX_EN_W<'_, CTRL_CFG_SPEC> {
        HW_AUTO_ACK_TX_EN_W::new(self, 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn hw_enhance_ack_tx_en(&mut self) -> HW_ENHANCE_ACK_TX_EN_W<'_, CTRL_CFG_SPEC> {
        HW_ENHANCE_ACK_TX_EN_W::new(self, 1)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn hw_auto_ack_rx_en(&mut self) -> HW_AUTO_ACK_RX_EN_W<'_, CTRL_CFG_SPEC> {
        HW_AUTO_ACK_RX_EN_W::new(self, 3)
    }
    #[doc = "Bit 5"]
    #[inline(always)]
    pub fn dis_ifs_control(&mut self) -> DIS_IFS_CONTROL_W<'_, CTRL_CFG_SPEC> {
        DIS_IFS_CONTROL_W::new(self, 5)
    }
    #[doc = "Bit 6"]
    #[inline(always)]
    pub fn pan_coordinator(&mut self) -> PAN_COORDINATOR_W<'_, CTRL_CFG_SPEC> {
        PAN_COORDINATOR_W::new(self, 6)
    }
    #[doc = "Bit 7"]
    #[inline(always)]
    pub fn promiscuous_mode(&mut self) -> PROMISCUOUS_MODE_W<'_, CTRL_CFG_SPEC> {
        PROMISCUOUS_MODE_W::new(self, 7)
    }
    #[doc = "Bit 11"]
    #[inline(always)]
    pub fn dis_frame_version_rsv_filter(
        &mut self,
    ) -> DIS_FRAME_VERSION_RSV_FILTER_W<'_, CTRL_CFG_SPEC> {
        DIS_FRAME_VERSION_RSV_FILTER_W::new(self, 11)
    }
    #[doc = "Bit 12"]
    #[inline(always)]
    pub fn autopend_enhance(&mut self) -> AUTOPEND_ENHANCE_W<'_, CTRL_CFG_SPEC> {
        AUTOPEND_ENHANCE_W::new(self, 12)
    }
    #[doc = "Bit 14"]
    #[inline(always)]
    pub fn filter_enhance(&mut self) -> FILTER_ENHANCE_W<'_, CTRL_CFG_SPEC> {
        FILTER_ENHANCE_W::new(self, 14)
    }
    #[doc = "Bits 16:20"]
    #[inline(always)]
    pub fn coex_arb_delay(&mut self) -> COEX_ARB_DELAY_W<'_, CTRL_CFG_SPEC> {
        COEX_ARB_DELAY_W::new(self, 16)
    }
    #[doc = "Bit 24"]
    #[inline(always)]
    pub fn bit_order(&mut self) -> BIT_ORDER_W<'_, CTRL_CFG_SPEC> {
        BIT_ORDER_W::new(self, 24)
    }
    #[doc = "Bit 25"]
    #[inline(always)]
    pub fn no_rss_trk_enb(&mut self) -> NO_RSS_TRK_ENB_W<'_, CTRL_CFG_SPEC> {
        NO_RSS_TRK_ENB_W::new(self, 25)
    }
    #[doc = "Bit 26"]
    #[inline(always)]
    pub fn force_rx_enb(&mut self) -> FORCE_RX_ENB_W<'_, CTRL_CFG_SPEC> {
        FORCE_RX_ENB_W::new(self, 26)
    }
    #[doc = "Bit 27"]
    #[inline(always)]
    pub fn rx_done_trigger_idle(&mut self) -> RX_DONE_TRIGGER_IDLE_W<'_, CTRL_CFG_SPEC> {
        RX_DONE_TRIGGER_IDLE_W::new(self, 27)
    }
    #[doc = "Bit 28"]
    #[inline(always)]
    pub fn mac_inf0_enable(&mut self) -> MAC_INF0_ENABLE_W<'_, CTRL_CFG_SPEC> {
        MAC_INF0_ENABLE_W::new(self, 28)
    }
    #[doc = "Bit 29"]
    #[inline(always)]
    pub fn mac_inf1_enable(&mut self) -> MAC_INF1_ENABLE_W<'_, CTRL_CFG_SPEC> {
        MAC_INF1_ENABLE_W::new(self, 29)
    }
    #[doc = "Bit 30"]
    #[inline(always)]
    pub fn mac_inf2_enable(&mut self) -> MAC_INF2_ENABLE_W<'_, CTRL_CFG_SPEC> {
        MAC_INF2_ENABLE_W::new(self, 30)
    }
    #[doc = "Bit 31"]
    #[inline(always)]
    pub fn mac_inf3_enable(&mut self) -> MAC_INF3_ENABLE_W<'_, CTRL_CFG_SPEC> {
        MAC_INF3_ENABLE_W::new(self, 31)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl_cfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl_cfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CTRL_CFG_SPEC;
impl crate::RegisterSpec for CTRL_CFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctrl_cfg::R`](R) reader structure"]
impl crate::Readable for CTRL_CFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ctrl_cfg::W`](W) writer structure"]
impl crate::Writable for CTRL_CFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CTRL_CFG to value 0"]
impl crate::Resettable for CTRL_CFG_SPEC {}
