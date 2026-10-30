#[doc = "Register `ERROR_CNT_CLEAR` reader"]
pub type R = crate::R<ERROR_CNT_CLEAR_SPEC>;
#[doc = "Register `ERROR_CNT_CLEAR` writer"]
pub type W = crate::W<ERROR_CNT_CLEAR_SPEC>;
#[doc = "Field `CCA_BUSY_CNT_CLEAR` reader - "]
pub type CCA_BUSY_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `CCA_BUSY_CNT_CLEAR` writer - "]
pub type CCA_BUSY_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_SECURITY_ERROR_CNT_CLEAR` reader - "]
pub type TX_SECURITY_ERROR_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `TX_SECURITY_ERROR_CNT_CLEAR` writer - "]
pub type TX_SECURITY_ERROR_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_BREAK_COEX_CNT_CLEAR` reader - "]
pub type TX_BREAK_COEX_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `TX_BREAK_COEX_CNT_CLEAR` writer - "]
pub type TX_BREAK_COEX_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_ACK_TIMEOUT_CNT_CLEAR` reader - "]
pub type RX_ACK_TIMEOUT_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `RX_ACK_TIMEOUT_CNT_CLEAR` writer - "]
pub type RX_ACK_TIMEOUT_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_ACK_ABORT_COEX_CNT_CLEAR` reader - "]
pub type RX_ACK_ABORT_COEX_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `RX_ACK_ABORT_COEX_CNT_CLEAR` writer - "]
pub type RX_ACK_ABORT_COEX_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ED_SCAN_COEX_CNT_CLEAR` reader - "]
pub type ED_SCAN_COEX_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `ED_SCAN_COEX_CNT_CLEAR` writer - "]
pub type ED_SCAN_COEX_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_ACK_ABORT_COEX_CNT_CLEAR` reader - "]
pub type TX_ACK_ABORT_COEX_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `TX_ACK_ABORT_COEX_CNT_CLEAR` writer - "]
pub type TX_ACK_ABORT_COEX_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_RESTART_CNT_CLEAR` reader - "]
pub type RX_RESTART_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `RX_RESTART_CNT_CLEAR` writer - "]
pub type RX_RESTART_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_ABORT_COEX_CNT_CLEAR` reader - "]
pub type RX_ABORT_COEX_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `RX_ABORT_COEX_CNT_CLEAR` writer - "]
pub type RX_ABORT_COEX_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NO_RSS_DETECT_CNT_CLEAR` reader - "]
pub type NO_RSS_DETECT_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `NO_RSS_DETECT_CNT_CLEAR` writer - "]
pub type NO_RSS_DETECT_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_FILTER_FAIL_CNT_CLEAR` reader - "]
pub type RX_FILTER_FAIL_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `RX_FILTER_FAIL_CNT_CLEAR` writer - "]
pub type RX_FILTER_FAIL_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CCA_FAIL_CNT_CLEAR` reader - "]
pub type CCA_FAIL_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `CCA_FAIL_CNT_CLEAR` writer - "]
pub type CCA_FAIL_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ED_ABORT_CNT_CLEAR` reader - "]
pub type ED_ABORT_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `ED_ABORT_CNT_CLEAR` writer - "]
pub type ED_ABORT_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CRC_ERROR_CNT_CLEAR` reader - "]
pub type CRC_ERROR_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `CRC_ERROR_CNT_CLEAR` writer - "]
pub type CRC_ERROR_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SFD_TIMEOUT_CNT_CLEAR` reader - "]
pub type SFD_TIMEOUT_CNT_CLEAR_R = crate::BitReader;
#[doc = "Field `SFD_TIMEOUT_CNT_CLEAR` writer - "]
pub type SFD_TIMEOUT_CNT_CLEAR_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn cca_busy_cnt_clear(&self) -> CCA_BUSY_CNT_CLEAR_R {
        CCA_BUSY_CNT_CLEAR_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn tx_security_error_cnt_clear(&self) -> TX_SECURITY_ERROR_CNT_CLEAR_R {
        TX_SECURITY_ERROR_CNT_CLEAR_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2"]
    #[inline(always)]
    pub fn tx_break_coex_cnt_clear(&self) -> TX_BREAK_COEX_CNT_CLEAR_R {
        TX_BREAK_COEX_CNT_CLEAR_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn rx_ack_timeout_cnt_clear(&self) -> RX_ACK_TIMEOUT_CNT_CLEAR_R {
        RX_ACK_TIMEOUT_CNT_CLEAR_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4"]
    #[inline(always)]
    pub fn rx_ack_abort_coex_cnt_clear(&self) -> RX_ACK_ABORT_COEX_CNT_CLEAR_R {
        RX_ACK_ABORT_COEX_CNT_CLEAR_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5"]
    #[inline(always)]
    pub fn ed_scan_coex_cnt_clear(&self) -> ED_SCAN_COEX_CNT_CLEAR_R {
        ED_SCAN_COEX_CNT_CLEAR_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6"]
    #[inline(always)]
    pub fn tx_ack_abort_coex_cnt_clear(&self) -> TX_ACK_ABORT_COEX_CNT_CLEAR_R {
        TX_ACK_ABORT_COEX_CNT_CLEAR_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7"]
    #[inline(always)]
    pub fn rx_restart_cnt_clear(&self) -> RX_RESTART_CNT_CLEAR_R {
        RX_RESTART_CNT_CLEAR_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8"]
    #[inline(always)]
    pub fn rx_abort_coex_cnt_clear(&self) -> RX_ABORT_COEX_CNT_CLEAR_R {
        RX_ABORT_COEX_CNT_CLEAR_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9"]
    #[inline(always)]
    pub fn no_rss_detect_cnt_clear(&self) -> NO_RSS_DETECT_CNT_CLEAR_R {
        NO_RSS_DETECT_CNT_CLEAR_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10"]
    #[inline(always)]
    pub fn rx_filter_fail_cnt_clear(&self) -> RX_FILTER_FAIL_CNT_CLEAR_R {
        RX_FILTER_FAIL_CNT_CLEAR_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11"]
    #[inline(always)]
    pub fn cca_fail_cnt_clear(&self) -> CCA_FAIL_CNT_CLEAR_R {
        CCA_FAIL_CNT_CLEAR_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12"]
    #[inline(always)]
    pub fn ed_abort_cnt_clear(&self) -> ED_ABORT_CNT_CLEAR_R {
        ED_ABORT_CNT_CLEAR_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13"]
    #[inline(always)]
    pub fn crc_error_cnt_clear(&self) -> CRC_ERROR_CNT_CLEAR_R {
        CRC_ERROR_CNT_CLEAR_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14"]
    #[inline(always)]
    pub fn sfd_timeout_cnt_clear(&self) -> SFD_TIMEOUT_CNT_CLEAR_R {
        SFD_TIMEOUT_CNT_CLEAR_R::new(((self.bits >> 14) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ERROR_CNT_CLEAR")
            .field("cca_busy_cnt_clear", &self.cca_busy_cnt_clear())
            .field(
                "tx_security_error_cnt_clear",
                &self.tx_security_error_cnt_clear(),
            )
            .field("tx_break_coex_cnt_clear", &self.tx_break_coex_cnt_clear())
            .field("rx_ack_timeout_cnt_clear", &self.rx_ack_timeout_cnt_clear())
            .field(
                "rx_ack_abort_coex_cnt_clear",
                &self.rx_ack_abort_coex_cnt_clear(),
            )
            .field("ed_scan_coex_cnt_clear", &self.ed_scan_coex_cnt_clear())
            .field(
                "tx_ack_abort_coex_cnt_clear",
                &self.tx_ack_abort_coex_cnt_clear(),
            )
            .field("rx_restart_cnt_clear", &self.rx_restart_cnt_clear())
            .field("rx_abort_coex_cnt_clear", &self.rx_abort_coex_cnt_clear())
            .field("no_rss_detect_cnt_clear", &self.no_rss_detect_cnt_clear())
            .field("rx_filter_fail_cnt_clear", &self.rx_filter_fail_cnt_clear())
            .field("cca_fail_cnt_clear", &self.cca_fail_cnt_clear())
            .field("ed_abort_cnt_clear", &self.ed_abort_cnt_clear())
            .field("crc_error_cnt_clear", &self.crc_error_cnt_clear())
            .field("sfd_timeout_cnt_clear", &self.sfd_timeout_cnt_clear())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0"]
    #[inline(always)]
    pub fn cca_busy_cnt_clear(&mut self) -> CCA_BUSY_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        CCA_BUSY_CNT_CLEAR_W::new(self, 0)
    }
    #[doc = "Bit 1"]
    #[inline(always)]
    pub fn tx_security_error_cnt_clear(
        &mut self,
    ) -> TX_SECURITY_ERROR_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        TX_SECURITY_ERROR_CNT_CLEAR_W::new(self, 1)
    }
    #[doc = "Bit 2"]
    #[inline(always)]
    pub fn tx_break_coex_cnt_clear(
        &mut self,
    ) -> TX_BREAK_COEX_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        TX_BREAK_COEX_CNT_CLEAR_W::new(self, 2)
    }
    #[doc = "Bit 3"]
    #[inline(always)]
    pub fn rx_ack_timeout_cnt_clear(
        &mut self,
    ) -> RX_ACK_TIMEOUT_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        RX_ACK_TIMEOUT_CNT_CLEAR_W::new(self, 3)
    }
    #[doc = "Bit 4"]
    #[inline(always)]
    pub fn rx_ack_abort_coex_cnt_clear(
        &mut self,
    ) -> RX_ACK_ABORT_COEX_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        RX_ACK_ABORT_COEX_CNT_CLEAR_W::new(self, 4)
    }
    #[doc = "Bit 5"]
    #[inline(always)]
    pub fn ed_scan_coex_cnt_clear(&mut self) -> ED_SCAN_COEX_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        ED_SCAN_COEX_CNT_CLEAR_W::new(self, 5)
    }
    #[doc = "Bit 6"]
    #[inline(always)]
    pub fn tx_ack_abort_coex_cnt_clear(
        &mut self,
    ) -> TX_ACK_ABORT_COEX_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        TX_ACK_ABORT_COEX_CNT_CLEAR_W::new(self, 6)
    }
    #[doc = "Bit 7"]
    #[inline(always)]
    pub fn rx_restart_cnt_clear(&mut self) -> RX_RESTART_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        RX_RESTART_CNT_CLEAR_W::new(self, 7)
    }
    #[doc = "Bit 8"]
    #[inline(always)]
    pub fn rx_abort_coex_cnt_clear(
        &mut self,
    ) -> RX_ABORT_COEX_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        RX_ABORT_COEX_CNT_CLEAR_W::new(self, 8)
    }
    #[doc = "Bit 9"]
    #[inline(always)]
    pub fn no_rss_detect_cnt_clear(
        &mut self,
    ) -> NO_RSS_DETECT_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        NO_RSS_DETECT_CNT_CLEAR_W::new(self, 9)
    }
    #[doc = "Bit 10"]
    #[inline(always)]
    pub fn rx_filter_fail_cnt_clear(
        &mut self,
    ) -> RX_FILTER_FAIL_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        RX_FILTER_FAIL_CNT_CLEAR_W::new(self, 10)
    }
    #[doc = "Bit 11"]
    #[inline(always)]
    pub fn cca_fail_cnt_clear(&mut self) -> CCA_FAIL_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        CCA_FAIL_CNT_CLEAR_W::new(self, 11)
    }
    #[doc = "Bit 12"]
    #[inline(always)]
    pub fn ed_abort_cnt_clear(&mut self) -> ED_ABORT_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        ED_ABORT_CNT_CLEAR_W::new(self, 12)
    }
    #[doc = "Bit 13"]
    #[inline(always)]
    pub fn crc_error_cnt_clear(&mut self) -> CRC_ERROR_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        CRC_ERROR_CNT_CLEAR_W::new(self, 13)
    }
    #[doc = "Bit 14"]
    #[inline(always)]
    pub fn sfd_timeout_cnt_clear(&mut self) -> SFD_TIMEOUT_CNT_CLEAR_W<'_, ERROR_CNT_CLEAR_SPEC> {
        SFD_TIMEOUT_CNT_CLEAR_W::new(self, 14)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`error_cnt_clear::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`error_cnt_clear::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ERROR_CNT_CLEAR_SPEC;
impl crate::RegisterSpec for ERROR_CNT_CLEAR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`error_cnt_clear::R`](R) reader structure"]
impl crate::Readable for ERROR_CNT_CLEAR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`error_cnt_clear::W`](W) writer structure"]
impl crate::Writable for ERROR_CNT_CLEAR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ERROR_CNT_CLEAR to value 0"]
impl crate::Resettable for ERROR_CNT_CLEAR_SPEC {}
