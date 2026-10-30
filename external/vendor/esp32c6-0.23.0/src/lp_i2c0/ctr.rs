#[doc = "Register `CTR` reader"]
pub type R = crate::R<CTR_SPEC>;
#[doc = "Register `CTR` writer"]
pub type W = crate::W<CTR_SPEC>;
#[doc = "Field `SDA_FORCE_OUT` reader - 1: direct output, 0: open drain output."]
pub type SDA_FORCE_OUT_R = crate::BitReader;
#[doc = "Field `SDA_FORCE_OUT` writer - 1: direct output, 0: open drain output."]
pub type SDA_FORCE_OUT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SCL_FORCE_OUT` reader - 1: direct output, 0: open drain output."]
pub type SCL_FORCE_OUT_R = crate::BitReader;
#[doc = "Field `SCL_FORCE_OUT` writer - 1: direct output, 0: open drain output."]
pub type SCL_FORCE_OUT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SAMPLE_SCL_LEVEL` reader - This register is used to select the sample mode. 1: sample SDA data on the SCL low level. 0: sample SDA data on the SCL high level."]
pub type SAMPLE_SCL_LEVEL_R = crate::BitReader;
#[doc = "Field `SAMPLE_SCL_LEVEL` writer - This register is used to select the sample mode. 1: sample SDA data on the SCL low level. 0: sample SDA data on the SCL high level."]
pub type SAMPLE_SCL_LEVEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_FULL_ACK_LEVEL` reader - This register is used to configure the ACK value that need to sent by master when the rx_fifo_cnt has reached the threshold."]
pub type RX_FULL_ACK_LEVEL_R = crate::BitReader;
#[doc = "Field `RX_FULL_ACK_LEVEL` writer - This register is used to configure the ACK value that need to sent by master when the rx_fifo_cnt has reached the threshold."]
pub type RX_FULL_ACK_LEVEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TRANS_START` writer - Set this bit to start sending the data in txfifo."]
pub type TRANS_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_LSB_FIRST` reader - This bit is used to control the sending mode for data needing to be sent. 1: send data from the least significant bit, 0: send data from the most significant bit."]
pub type TX_LSB_FIRST_R = crate::BitReader;
#[doc = "Field `TX_LSB_FIRST` writer - This bit is used to control the sending mode for data needing to be sent. 1: send data from the least significant bit, 0: send data from the most significant bit."]
pub type TX_LSB_FIRST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_LSB_FIRST` reader - This bit is used to control the storage mode for received data. 1: receive data from the least significant bit, 0: receive data from the most significant bit."]
pub type RX_LSB_FIRST_R = crate::BitReader;
#[doc = "Field `RX_LSB_FIRST` writer - This bit is used to control the storage mode for received data. 1: receive data from the least significant bit, 0: receive data from the most significant bit."]
pub type RX_LSB_FIRST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLK_EN` reader - Reserved"]
pub type CLK_EN_R = crate::BitReader;
#[doc = "Field `CLK_EN` writer - Reserved"]
pub type CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ARBITRATION_EN` reader - This is the enable bit for arbitration_lost."]
pub type ARBITRATION_EN_R = crate::BitReader;
#[doc = "Field `ARBITRATION_EN` writer - This is the enable bit for arbitration_lost."]
pub type ARBITRATION_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FSM_RST` writer - This register is used to reset the scl FMS."]
pub type FSM_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CONF_UPGATE` writer - synchronization bit"]
pub type CONF_UPGATE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - 1: direct output, 0: open drain output."]
    #[inline(always)]
    pub fn sda_force_out(&self) -> SDA_FORCE_OUT_R {
        SDA_FORCE_OUT_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - 1: direct output, 0: open drain output."]
    #[inline(always)]
    pub fn scl_force_out(&self) -> SCL_FORCE_OUT_R {
        SCL_FORCE_OUT_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - This register is used to select the sample mode. 1: sample SDA data on the SCL low level. 0: sample SDA data on the SCL high level."]
    #[inline(always)]
    pub fn sample_scl_level(&self) -> SAMPLE_SCL_LEVEL_R {
        SAMPLE_SCL_LEVEL_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - This register is used to configure the ACK value that need to sent by master when the rx_fifo_cnt has reached the threshold."]
    #[inline(always)]
    pub fn rx_full_ack_level(&self) -> RX_FULL_ACK_LEVEL_R {
        RX_FULL_ACK_LEVEL_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 6 - This bit is used to control the sending mode for data needing to be sent. 1: send data from the least significant bit, 0: send data from the most significant bit."]
    #[inline(always)]
    pub fn tx_lsb_first(&self) -> TX_LSB_FIRST_R {
        TX_LSB_FIRST_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - This bit is used to control the storage mode for received data. 1: receive data from the least significant bit, 0: receive data from the most significant bit."]
    #[inline(always)]
    pub fn rx_lsb_first(&self) -> RX_LSB_FIRST_R {
        RX_LSB_FIRST_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Reserved"]
    #[inline(always)]
    pub fn clk_en(&self) -> CLK_EN_R {
        CLK_EN_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - This is the enable bit for arbitration_lost."]
    #[inline(always)]
    pub fn arbitration_en(&self) -> ARBITRATION_EN_R {
        ARBITRATION_EN_R::new(((self.bits >> 9) & 1) != 0)
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
            .field("tx_lsb_first", &self.tx_lsb_first())
            .field("rx_lsb_first", &self.rx_lsb_first())
            .field("clk_en", &self.clk_en())
            .field("arbitration_en", &self.arbitration_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - 1: direct output, 0: open drain output."]
    #[inline(always)]
    pub fn sda_force_out(&mut self) -> SDA_FORCE_OUT_W<'_, CTR_SPEC> {
        SDA_FORCE_OUT_W::new(self, 0)
    }
    #[doc = "Bit 1 - 1: direct output, 0: open drain output."]
    #[inline(always)]
    pub fn scl_force_out(&mut self) -> SCL_FORCE_OUT_W<'_, CTR_SPEC> {
        SCL_FORCE_OUT_W::new(self, 1)
    }
    #[doc = "Bit 2 - This register is used to select the sample mode. 1: sample SDA data on the SCL low level. 0: sample SDA data on the SCL high level."]
    #[inline(always)]
    pub fn sample_scl_level(&mut self) -> SAMPLE_SCL_LEVEL_W<'_, CTR_SPEC> {
        SAMPLE_SCL_LEVEL_W::new(self, 2)
    }
    #[doc = "Bit 3 - This register is used to configure the ACK value that need to sent by master when the rx_fifo_cnt has reached the threshold."]
    #[inline(always)]
    pub fn rx_full_ack_level(&mut self) -> RX_FULL_ACK_LEVEL_W<'_, CTR_SPEC> {
        RX_FULL_ACK_LEVEL_W::new(self, 3)
    }
    #[doc = "Bit 5 - Set this bit to start sending the data in txfifo."]
    #[inline(always)]
    pub fn trans_start(&mut self) -> TRANS_START_W<'_, CTR_SPEC> {
        TRANS_START_W::new(self, 5)
    }
    #[doc = "Bit 6 - This bit is used to control the sending mode for data needing to be sent. 1: send data from the least significant bit, 0: send data from the most significant bit."]
    #[inline(always)]
    pub fn tx_lsb_first(&mut self) -> TX_LSB_FIRST_W<'_, CTR_SPEC> {
        TX_LSB_FIRST_W::new(self, 6)
    }
    #[doc = "Bit 7 - This bit is used to control the storage mode for received data. 1: receive data from the least significant bit, 0: receive data from the most significant bit."]
    #[inline(always)]
    pub fn rx_lsb_first(&mut self) -> RX_LSB_FIRST_W<'_, CTR_SPEC> {
        RX_LSB_FIRST_W::new(self, 7)
    }
    #[doc = "Bit 8 - Reserved"]
    #[inline(always)]
    pub fn clk_en(&mut self) -> CLK_EN_W<'_, CTR_SPEC> {
        CLK_EN_W::new(self, 8)
    }
    #[doc = "Bit 9 - This is the enable bit for arbitration_lost."]
    #[inline(always)]
    pub fn arbitration_en(&mut self) -> ARBITRATION_EN_W<'_, CTR_SPEC> {
        ARBITRATION_EN_W::new(self, 9)
    }
    #[doc = "Bit 10 - This register is used to reset the scl FMS."]
    #[inline(always)]
    pub fn fsm_rst(&mut self) -> FSM_RST_W<'_, CTR_SPEC> {
        FSM_RST_W::new(self, 10)
    }
    #[doc = "Bit 11 - synchronization bit"]
    #[inline(always)]
    pub fn conf_upgate(&mut self) -> CONF_UPGATE_W<'_, CTR_SPEC> {
        CONF_UPGATE_W::new(self, 11)
    }
}
#[doc = "Transmission setting\n\nYou can [`read`](crate::Reg::read) this register and get [`ctr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
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
#[doc = "`reset()` method sets CTR to value 0x0208"]
impl crate::Resettable for CTR_SPEC {
    const RESET_VALUE: u32 = 0x0208;
}
