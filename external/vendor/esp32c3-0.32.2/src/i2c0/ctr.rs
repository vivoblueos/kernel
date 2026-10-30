#[doc = "Register `CTR` reader"]
pub type R = crate::R<CTR_SPEC>;
#[doc = "Register `CTR` writer"]
pub type W = crate::W<CTR_SPEC>;
#[doc = "Field `SDA_FORCE_OUT` reader - reg_sda_force_out"]
pub type SDA_FORCE_OUT_R = crate::BitReader;
#[doc = "Field `SDA_FORCE_OUT` writer - reg_sda_force_out"]
pub type SDA_FORCE_OUT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SCL_FORCE_OUT` reader - reg_scl_force_out"]
pub type SCL_FORCE_OUT_R = crate::BitReader;
#[doc = "Field `SCL_FORCE_OUT` writer - reg_scl_force_out"]
pub type SCL_FORCE_OUT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAMPLE_SCL_LEVEL` reader - reg_sample_scl_level"]
pub type SAMPLE_SCL_LEVEL_R = crate::BitReader;
#[doc = "Field `SAMPLE_SCL_LEVEL` writer - reg_sample_scl_level"]
pub type SAMPLE_SCL_LEVEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_FULL_ACK_LEVEL` reader - reg_rx_full_ack_level"]
pub type RX_FULL_ACK_LEVEL_R = crate::BitReader;
#[doc = "Field `RX_FULL_ACK_LEVEL` writer - reg_rx_full_ack_level"]
pub type RX_FULL_ACK_LEVEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MS_MODE` reader - reg_ms_mode"]
pub type MS_MODE_R = crate::BitReader;
#[doc = "Field `MS_MODE` writer - reg_ms_mode"]
pub type MS_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TRANS_START` writer - reg_trans_start"]
pub type TRANS_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_LSB_FIRST` reader - reg_tx_lsb_first"]
pub type TX_LSB_FIRST_R = crate::BitReader;
#[doc = "Field `TX_LSB_FIRST` writer - reg_tx_lsb_first"]
pub type TX_LSB_FIRST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_LSB_FIRST` reader - reg_rx_lsb_first"]
pub type RX_LSB_FIRST_R = crate::BitReader;
#[doc = "Field `RX_LSB_FIRST` writer - reg_rx_lsb_first"]
pub type RX_LSB_FIRST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_EN` reader - reg_clk_en"]
pub type CLK_EN_R = crate::BitReader;
#[doc = "Field `CLK_EN` writer - reg_clk_en"]
pub type CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ARBITRATION_EN` reader - reg_arbitration_en"]
pub type ARBITRATION_EN_R = crate::BitReader;
#[doc = "Field `ARBITRATION_EN` writer - reg_arbitration_en"]
pub type ARBITRATION_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FSM_RST` writer - reg_fsm_rst"]
pub type FSM_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CONF_UPGATE` writer - reg_conf_upgate"]
pub type CONF_UPGATE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLV_TX_AUTO_START_EN` reader - reg_slv_tx_auto_start_en"]
pub type SLV_TX_AUTO_START_EN_R = crate::BitReader;
#[doc = "Field `SLV_TX_AUTO_START_EN` writer - reg_slv_tx_auto_start_en"]
pub type SLV_TX_AUTO_START_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADDR_10BIT_RW_CHECK_EN` reader - reg_addr_10bit_rw_check_en"]
pub type ADDR_10BIT_RW_CHECK_EN_R = crate::BitReader;
#[doc = "Field `ADDR_10BIT_RW_CHECK_EN` writer - reg_addr_10bit_rw_check_en"]
pub type ADDR_10BIT_RW_CHECK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADDR_BROADCASTING_EN` reader - reg_addr_broadcasting_en"]
pub type ADDR_BROADCASTING_EN_R = crate::BitReader;
#[doc = "Field `ADDR_BROADCASTING_EN` writer - reg_addr_broadcasting_en"]
pub type ADDR_BROADCASTING_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - reg_sda_force_out"]
    #[inline(always)]
    pub fn sda_force_out(&self) -> SDA_FORCE_OUT_R {
        SDA_FORCE_OUT_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - reg_scl_force_out"]
    #[inline(always)]
    pub fn scl_force_out(&self) -> SCL_FORCE_OUT_R {
        SCL_FORCE_OUT_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - reg_sample_scl_level"]
    #[inline(always)]
    pub fn sample_scl_level(&self) -> SAMPLE_SCL_LEVEL_R {
        SAMPLE_SCL_LEVEL_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - reg_rx_full_ack_level"]
    #[inline(always)]
    pub fn rx_full_ack_level(&self) -> RX_FULL_ACK_LEVEL_R {
        RX_FULL_ACK_LEVEL_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - reg_ms_mode"]
    #[inline(always)]
    pub fn ms_mode(&self) -> MS_MODE_R {
        MS_MODE_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 6 - reg_tx_lsb_first"]
    #[inline(always)]
    pub fn tx_lsb_first(&self) -> TX_LSB_FIRST_R {
        TX_LSB_FIRST_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - reg_rx_lsb_first"]
    #[inline(always)]
    pub fn rx_lsb_first(&self) -> RX_LSB_FIRST_R {
        RX_LSB_FIRST_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - reg_clk_en"]
    #[inline(always)]
    pub fn clk_en(&self) -> CLK_EN_R {
        CLK_EN_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - reg_arbitration_en"]
    #[inline(always)]
    pub fn arbitration_en(&self) -> ARBITRATION_EN_R {
        ARBITRATION_EN_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 12 - reg_slv_tx_auto_start_en"]
    #[inline(always)]
    pub fn slv_tx_auto_start_en(&self) -> SLV_TX_AUTO_START_EN_R {
        SLV_TX_AUTO_START_EN_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - reg_addr_10bit_rw_check_en"]
    #[inline(always)]
    pub fn addr_10bit_rw_check_en(&self) -> ADDR_10BIT_RW_CHECK_EN_R {
        ADDR_10BIT_RW_CHECK_EN_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - reg_addr_broadcasting_en"]
    #[inline(always)]
    pub fn addr_broadcasting_en(&self) -> ADDR_BROADCASTING_EN_R {
        ADDR_BROADCASTING_EN_R::new(((self.bits >> 14) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CTR")
            .field("sda_force_out", &self.sda_force_out())
            .field("scl_force_out", &self.scl_force_out())
            .field("sample_scl_level", &self.sample_scl_level())
            .field("rx_full_ack_level", &self.rx_full_ack_level())
            .field("ms_mode", &self.ms_mode())
            .field("tx_lsb_first", &self.tx_lsb_first())
            .field("rx_lsb_first", &self.rx_lsb_first())
            .field("clk_en", &self.clk_en())
            .field("arbitration_en", &self.arbitration_en())
            .field("slv_tx_auto_start_en", &self.slv_tx_auto_start_en())
            .field("addr_10bit_rw_check_en", &self.addr_10bit_rw_check_en())
            .field("addr_broadcasting_en", &self.addr_broadcasting_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - reg_sda_force_out"]
    #[inline(always)]
    pub fn sda_force_out(&mut self) -> SDA_FORCE_OUT_W<'_, CTR_SPEC> {
        SDA_FORCE_OUT_W::new(self, 0)
    }
    #[doc = "Bit 1 - reg_scl_force_out"]
    #[inline(always)]
    pub fn scl_force_out(&mut self) -> SCL_FORCE_OUT_W<'_, CTR_SPEC> {
        SCL_FORCE_OUT_W::new(self, 1)
    }
    #[doc = "Bit 2 - reg_sample_scl_level"]
    #[inline(always)]
    pub fn sample_scl_level(&mut self) -> SAMPLE_SCL_LEVEL_W<'_, CTR_SPEC> {
        SAMPLE_SCL_LEVEL_W::new(self, 2)
    }
    #[doc = "Bit 3 - reg_rx_full_ack_level"]
    #[inline(always)]
    pub fn rx_full_ack_level(&mut self) -> RX_FULL_ACK_LEVEL_W<'_, CTR_SPEC> {
        RX_FULL_ACK_LEVEL_W::new(self, 3)
    }
    #[doc = "Bit 4 - reg_ms_mode"]
    #[inline(always)]
    pub fn ms_mode(&mut self) -> MS_MODE_W<'_, CTR_SPEC> {
        MS_MODE_W::new(self, 4)
    }
    #[doc = "Bit 5 - reg_trans_start"]
    #[inline(always)]
    pub fn trans_start(&mut self) -> TRANS_START_W<'_, CTR_SPEC> {
        TRANS_START_W::new(self, 5)
    }
    #[doc = "Bit 6 - reg_tx_lsb_first"]
    #[inline(always)]
    pub fn tx_lsb_first(&mut self) -> TX_LSB_FIRST_W<'_, CTR_SPEC> {
        TX_LSB_FIRST_W::new(self, 6)
    }
    #[doc = "Bit 7 - reg_rx_lsb_first"]
    #[inline(always)]
    pub fn rx_lsb_first(&mut self) -> RX_LSB_FIRST_W<'_, CTR_SPEC> {
        RX_LSB_FIRST_W::new(self, 7)
    }
    #[doc = "Bit 8 - reg_clk_en"]
    #[inline(always)]
    pub fn clk_en(&mut self) -> CLK_EN_W<'_, CTR_SPEC> {
        CLK_EN_W::new(self, 8)
    }
    #[doc = "Bit 9 - reg_arbitration_en"]
    #[inline(always)]
    pub fn arbitration_en(&mut self) -> ARBITRATION_EN_W<'_, CTR_SPEC> {
        ARBITRATION_EN_W::new(self, 9)
    }
    #[doc = "Bit 10 - reg_fsm_rst"]
    #[inline(always)]
    pub fn fsm_rst(&mut self) -> FSM_RST_W<'_, CTR_SPEC> {
        FSM_RST_W::new(self, 10)
    }
    #[doc = "Bit 11 - reg_conf_upgate"]
    #[inline(always)]
    pub fn conf_upgate(&mut self) -> CONF_UPGATE_W<'_, CTR_SPEC> {
        CONF_UPGATE_W::new(self, 11)
    }
    #[doc = "Bit 12 - reg_slv_tx_auto_start_en"]
    #[inline(always)]
    pub fn slv_tx_auto_start_en(&mut self) -> SLV_TX_AUTO_START_EN_W<'_, CTR_SPEC> {
        SLV_TX_AUTO_START_EN_W::new(self, 12)
    }
    #[doc = "Bit 13 - reg_addr_10bit_rw_check_en"]
    #[inline(always)]
    pub fn addr_10bit_rw_check_en(&mut self) -> ADDR_10BIT_RW_CHECK_EN_W<'_, CTR_SPEC> {
        ADDR_10BIT_RW_CHECK_EN_W::new(self, 13)
    }
    #[doc = "Bit 14 - reg_addr_broadcasting_en"]
    #[inline(always)]
    pub fn addr_broadcasting_en(&mut self) -> ADDR_BROADCASTING_EN_W<'_, CTR_SPEC> {
        ADDR_BROADCASTING_EN_W::new(self, 14)
    }
}
#[doc = "I2C_CTR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`ctr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CTR_SPEC;
impl crate::RegisterSpec for CTR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctr::R`](R) reader structure"]
impl crate::Readable for CTR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ctr::W`](W) writer structure"]
impl crate::Writable for CTR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CTR to value 0x020b"]
impl crate::Resettable for CTR_SPEC {
    const RESET_VALUE: u32 = 0x020b;
}
