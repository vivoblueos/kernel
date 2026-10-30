#[doc = "Register `TX_CONF` reader"]
pub type R = crate::R<TX_CONF_SPEC>;
#[doc = "Register `TX_CONF` writer"]
pub type W = crate::W<TX_CONF_SPEC>;
#[doc = "Field `TX_RESET` writer - Set this bit to reset transmitter"]
pub type TX_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_FIFO_RESET` writer - Set this bit to reset Tx AFIFO"]
pub type TX_FIFO_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_START` reader - Set this bit to start transmitting data"]
pub type TX_START_R = crate::BitReader;
#[doc = "Field `TX_START` writer - Set this bit to start transmitting data"]
pub type TX_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_SLAVE_MOD` reader - Set this bit to enable slave transmitter mode"]
pub type TX_SLAVE_MOD_R = crate::BitReader;
#[doc = "Field `TX_SLAVE_MOD` writer - Set this bit to enable slave transmitter mode"]
pub type TX_SLAVE_MOD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_MONO` reader - Set this bit to enable transmitter in mono mode"]
pub type TX_MONO_R = crate::BitReader;
#[doc = "Field `TX_MONO` writer - Set this bit to enable transmitter in mono mode"]
pub type TX_MONO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_CHAN_EQUAL` reader - 1: The value of Left channel data is equal to the value of right channel data in I2S TX mono mode or TDM channel select mode. 0: The invalid channel data is reg_i2s_single_data in I2S TX mono mode or TDM channel select mode."]
pub type TX_CHAN_EQUAL_R = crate::BitReader;
#[doc = "Field `TX_CHAN_EQUAL` writer - 1: The value of Left channel data is equal to the value of right channel data in I2S TX mono mode or TDM channel select mode. 0: The invalid channel data is reg_i2s_single_data in I2S TX mono mode or TDM channel select mode."]
pub type TX_CHAN_EQUAL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_BIG_ENDIAN` reader - I2S Tx byte endian, 1: low addr value to high addr. 0: low addr with low addr value."]
pub type TX_BIG_ENDIAN_R = crate::BitReader;
#[doc = "Field `TX_BIG_ENDIAN` writer - I2S Tx byte endian, 1: low addr value to high addr. 0: low addr with low addr value."]
pub type TX_BIG_ENDIAN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_UPDATE` reader - Set 1 to update I2S TX registers from APB clock domain to I2S TX clock domain. This bit will be cleared by hardware after update register done."]
pub type TX_UPDATE_R = crate::BitReader;
#[doc = "Field `TX_UPDATE` writer - Set 1 to update I2S TX registers from APB clock domain to I2S TX clock domain. This bit will be cleared by hardware after update register done."]
pub type TX_UPDATE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_MONO_FST_VLD` reader - 1: The first channel data value is valid in I2S TX mono mode. 0: The second channel data value is valid in I2S TX mono mode."]
pub type TX_MONO_FST_VLD_R = crate::BitReader;
#[doc = "Field `TX_MONO_FST_VLD` writer - 1: The first channel data value is valid in I2S TX mono mode. 0: The second channel data value is valid in I2S TX mono mode."]
pub type TX_MONO_FST_VLD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_PCM_CONF` reader - I2S TX compress/decompress configuration bit. & 0 (atol): A-Law decompress, 1 (ltoa) : A-Law compress, 2 (utol) : u-Law decompress, 3 (ltou) : u-Law compress. &"]
pub type TX_PCM_CONF_R = crate::FieldReader;
#[doc = "Field `TX_PCM_CONF` writer - I2S TX compress/decompress configuration bit. & 0 (atol): A-Law decompress, 1 (ltoa) : A-Law compress, 2 (utol) : u-Law decompress, 3 (ltou) : u-Law compress. &"]
pub type TX_PCM_CONF_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `TX_PCM_BYPASS` reader - Set this bit to bypass Compress/Decompress module for transmitted data."]
pub type TX_PCM_BYPASS_R = crate::BitReader;
#[doc = "Field `TX_PCM_BYPASS` writer - Set this bit to bypass Compress/Decompress module for transmitted data."]
pub type TX_PCM_BYPASS_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_STOP_EN` reader - Set this bit to stop disable output BCK signal and WS signal when tx FIFO is emtpy"]
pub type TX_STOP_EN_R = crate::BitReader;
#[doc = "Field `TX_STOP_EN` writer - Set this bit to stop disable output BCK signal and WS signal when tx FIFO is emtpy"]
pub type TX_STOP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_LEFT_ALIGN` reader - 1: I2S TX left alignment mode. 0: I2S TX right alignment mode."]
pub type TX_LEFT_ALIGN_R = crate::BitReader;
#[doc = "Field `TX_LEFT_ALIGN` writer - 1: I2S TX left alignment mode. 0: I2S TX right alignment mode."]
pub type TX_LEFT_ALIGN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_24_FILL_EN` reader - 1: Sent 32 bits in 24 channel bits mode. 0: Sent 24 bits in 24 channel bits mode"]
pub type TX_24_FILL_EN_R = crate::BitReader;
#[doc = "Field `TX_24_FILL_EN` writer - 1: Sent 32 bits in 24 channel bits mode. 0: Sent 24 bits in 24 channel bits mode"]
pub type TX_24_FILL_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_WS_IDLE_POL` reader - 0: WS should be 0 when sending left channel data, and WS is 1in right channel. 1: WS should be 1 when sending left channel data, and WS is 0in right channel."]
pub type TX_WS_IDLE_POL_R = crate::BitReader;
#[doc = "Field `TX_WS_IDLE_POL` writer - 0: WS should be 0 when sending left channel data, and WS is 1in right channel. 1: WS should be 1 when sending left channel data, and WS is 0in right channel."]
pub type TX_WS_IDLE_POL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_BIT_ORDER` reader - I2S Tx bit endian. 1:small endian, the LSB is sent first. 0:big endian, the MSB is sent first."]
pub type TX_BIT_ORDER_R = crate::BitReader;
#[doc = "Field `TX_BIT_ORDER` writer - I2S Tx bit endian. 1:small endian, the LSB is sent first. 0:big endian, the MSB is sent first."]
pub type TX_BIT_ORDER_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_TDM_EN` reader - 1: Enable I2S TDM Tx mode . 0: Disable."]
pub type TX_TDM_EN_R = crate::BitReader;
#[doc = "Field `TX_TDM_EN` writer - 1: Enable I2S TDM Tx mode . 0: Disable."]
pub type TX_TDM_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_PDM_EN` reader - 1: Enable I2S PDM Tx mode . 0: Disable."]
pub type TX_PDM_EN_R = crate::BitReader;
#[doc = "Field `TX_PDM_EN` writer - 1: Enable I2S PDM Tx mode . 0: Disable."]
pub type TX_PDM_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_CHAN_MOD` reader - I2S transmitter channel mode configuration bits."]
pub type TX_CHAN_MOD_R = crate::FieldReader;
#[doc = "Field `TX_CHAN_MOD` writer - I2S transmitter channel mode configuration bits."]
pub type TX_CHAN_MOD_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SIG_LOOPBACK` reader - Enable signal loop back mode with transmitter module and receiver module sharing the same WS and BCK signals."]
pub type SIG_LOOPBACK_R = crate::BitReader;
#[doc = "Field `SIG_LOOPBACK` writer - Enable signal loop back mode with transmitter module and receiver module sharing the same WS and BCK signals."]
pub type SIG_LOOPBACK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 2 - Set this bit to start transmitting data"]
    #[inline(always)]
    pub fn tx_start(&self) -> TX_START_R {
        TX_START_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Set this bit to enable slave transmitter mode"]
    #[inline(always)]
    pub fn tx_slave_mod(&self) -> TX_SLAVE_MOD_R {
        TX_SLAVE_MOD_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 5 - Set this bit to enable transmitter in mono mode"]
    #[inline(always)]
    pub fn tx_mono(&self) -> TX_MONO_R {
        TX_MONO_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - 1: The value of Left channel data is equal to the value of right channel data in I2S TX mono mode or TDM channel select mode. 0: The invalid channel data is reg_i2s_single_data in I2S TX mono mode or TDM channel select mode."]
    #[inline(always)]
    pub fn tx_chan_equal(&self) -> TX_CHAN_EQUAL_R {
        TX_CHAN_EQUAL_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - I2S Tx byte endian, 1: low addr value to high addr. 0: low addr with low addr value."]
    #[inline(always)]
    pub fn tx_big_endian(&self) -> TX_BIG_ENDIAN_R {
        TX_BIG_ENDIAN_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Set 1 to update I2S TX registers from APB clock domain to I2S TX clock domain. This bit will be cleared by hardware after update register done."]
    #[inline(always)]
    pub fn tx_update(&self) -> TX_UPDATE_R {
        TX_UPDATE_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - 1: The first channel data value is valid in I2S TX mono mode. 0: The second channel data value is valid in I2S TX mono mode."]
    #[inline(always)]
    pub fn tx_mono_fst_vld(&self) -> TX_MONO_FST_VLD_R {
        TX_MONO_FST_VLD_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bits 10:11 - I2S TX compress/decompress configuration bit. & 0 (atol): A-Law decompress, 1 (ltoa) : A-Law compress, 2 (utol) : u-Law decompress, 3 (ltou) : u-Law compress. &"]
    #[inline(always)]
    pub fn tx_pcm_conf(&self) -> TX_PCM_CONF_R {
        TX_PCM_CONF_R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bit 12 - Set this bit to bypass Compress/Decompress module for transmitted data."]
    #[inline(always)]
    pub fn tx_pcm_bypass(&self) -> TX_PCM_BYPASS_R {
        TX_PCM_BYPASS_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Set this bit to stop disable output BCK signal and WS signal when tx FIFO is emtpy"]
    #[inline(always)]
    pub fn tx_stop_en(&self) -> TX_STOP_EN_R {
        TX_STOP_EN_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 15 - 1: I2S TX left alignment mode. 0: I2S TX right alignment mode."]
    #[inline(always)]
    pub fn tx_left_align(&self) -> TX_LEFT_ALIGN_R {
        TX_LEFT_ALIGN_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - 1: Sent 32 bits in 24 channel bits mode. 0: Sent 24 bits in 24 channel bits mode"]
    #[inline(always)]
    pub fn tx_24_fill_en(&self) -> TX_24_FILL_EN_R {
        TX_24_FILL_EN_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - 0: WS should be 0 when sending left channel data, and WS is 1in right channel. 1: WS should be 1 when sending left channel data, and WS is 0in right channel."]
    #[inline(always)]
    pub fn tx_ws_idle_pol(&self) -> TX_WS_IDLE_POL_R {
        TX_WS_IDLE_POL_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - I2S Tx bit endian. 1:small endian, the LSB is sent first. 0:big endian, the MSB is sent first."]
    #[inline(always)]
    pub fn tx_bit_order(&self) -> TX_BIT_ORDER_R {
        TX_BIT_ORDER_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - 1: Enable I2S TDM Tx mode . 0: Disable."]
    #[inline(always)]
    pub fn tx_tdm_en(&self) -> TX_TDM_EN_R {
        TX_TDM_EN_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - 1: Enable I2S PDM Tx mode . 0: Disable."]
    #[inline(always)]
    pub fn tx_pdm_en(&self) -> TX_PDM_EN_R {
        TX_PDM_EN_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bits 24:26 - I2S transmitter channel mode configuration bits."]
    #[inline(always)]
    pub fn tx_chan_mod(&self) -> TX_CHAN_MOD_R {
        TX_CHAN_MOD_R::new(((self.bits >> 24) & 7) as u8)
    }
    #[doc = "Bit 27 - Enable signal loop back mode with transmitter module and receiver module sharing the same WS and BCK signals."]
    #[inline(always)]
    pub fn sig_loopback(&self) -> SIG_LOOPBACK_R {
        SIG_LOOPBACK_R::new(((self.bits >> 27) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_CONF")
            .field("tx_start", &self.tx_start())
            .field("tx_slave_mod", &self.tx_slave_mod())
            .field("tx_mono", &self.tx_mono())
            .field("tx_chan_equal", &self.tx_chan_equal())
            .field("tx_big_endian", &self.tx_big_endian())
            .field("tx_update", &self.tx_update())
            .field("tx_mono_fst_vld", &self.tx_mono_fst_vld())
            .field("tx_pcm_conf", &self.tx_pcm_conf())
            .field("tx_pcm_bypass", &self.tx_pcm_bypass())
            .field("tx_stop_en", &self.tx_stop_en())
            .field("tx_left_align", &self.tx_left_align())
            .field("tx_24_fill_en", &self.tx_24_fill_en())
            .field("tx_ws_idle_pol", &self.tx_ws_idle_pol())
            .field("tx_bit_order", &self.tx_bit_order())
            .field("tx_tdm_en", &self.tx_tdm_en())
            .field("tx_pdm_en", &self.tx_pdm_en())
            .field("tx_chan_mod", &self.tx_chan_mod())
            .field("sig_loopback", &self.sig_loopback())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit to reset transmitter"]
    #[inline(always)]
    pub fn tx_reset(&mut self) -> TX_RESET_W<'_, TX_CONF_SPEC> {
        TX_RESET_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set this bit to reset Tx AFIFO"]
    #[inline(always)]
    pub fn tx_fifo_reset(&mut self) -> TX_FIFO_RESET_W<'_, TX_CONF_SPEC> {
        TX_FIFO_RESET_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set this bit to start transmitting data"]
    #[inline(always)]
    pub fn tx_start(&mut self) -> TX_START_W<'_, TX_CONF_SPEC> {
        TX_START_W::new(self, 2)
    }
    #[doc = "Bit 3 - Set this bit to enable slave transmitter mode"]
    #[inline(always)]
    pub fn tx_slave_mod(&mut self) -> TX_SLAVE_MOD_W<'_, TX_CONF_SPEC> {
        TX_SLAVE_MOD_W::new(self, 3)
    }
    #[doc = "Bit 5 - Set this bit to enable transmitter in mono mode"]
    #[inline(always)]
    pub fn tx_mono(&mut self) -> TX_MONO_W<'_, TX_CONF_SPEC> {
        TX_MONO_W::new(self, 5)
    }
    #[doc = "Bit 6 - 1: The value of Left channel data is equal to the value of right channel data in I2S TX mono mode or TDM channel select mode. 0: The invalid channel data is reg_i2s_single_data in I2S TX mono mode or TDM channel select mode."]
    #[inline(always)]
    pub fn tx_chan_equal(&mut self) -> TX_CHAN_EQUAL_W<'_, TX_CONF_SPEC> {
        TX_CHAN_EQUAL_W::new(self, 6)
    }
    #[doc = "Bit 7 - I2S Tx byte endian, 1: low addr value to high addr. 0: low addr with low addr value."]
    #[inline(always)]
    pub fn tx_big_endian(&mut self) -> TX_BIG_ENDIAN_W<'_, TX_CONF_SPEC> {
        TX_BIG_ENDIAN_W::new(self, 7)
    }
    #[doc = "Bit 8 - Set 1 to update I2S TX registers from APB clock domain to I2S TX clock domain. This bit will be cleared by hardware after update register done."]
    #[inline(always)]
    pub fn tx_update(&mut self) -> TX_UPDATE_W<'_, TX_CONF_SPEC> {
        TX_UPDATE_W::new(self, 8)
    }
    #[doc = "Bit 9 - 1: The first channel data value is valid in I2S TX mono mode. 0: The second channel data value is valid in I2S TX mono mode."]
    #[inline(always)]
    pub fn tx_mono_fst_vld(&mut self) -> TX_MONO_FST_VLD_W<'_, TX_CONF_SPEC> {
        TX_MONO_FST_VLD_W::new(self, 9)
    }
    #[doc = "Bits 10:11 - I2S TX compress/decompress configuration bit. & 0 (atol): A-Law decompress, 1 (ltoa) : A-Law compress, 2 (utol) : u-Law decompress, 3 (ltou) : u-Law compress. &"]
    #[inline(always)]
    pub fn tx_pcm_conf(&mut self) -> TX_PCM_CONF_W<'_, TX_CONF_SPEC> {
        TX_PCM_CONF_W::new(self, 10)
    }
    #[doc = "Bit 12 - Set this bit to bypass Compress/Decompress module for transmitted data."]
    #[inline(always)]
    pub fn tx_pcm_bypass(&mut self) -> TX_PCM_BYPASS_W<'_, TX_CONF_SPEC> {
        TX_PCM_BYPASS_W::new(self, 12)
    }
    #[doc = "Bit 13 - Set this bit to stop disable output BCK signal and WS signal when tx FIFO is emtpy"]
    #[inline(always)]
    pub fn tx_stop_en(&mut self) -> TX_STOP_EN_W<'_, TX_CONF_SPEC> {
        TX_STOP_EN_W::new(self, 13)
    }
    #[doc = "Bit 15 - 1: I2S TX left alignment mode. 0: I2S TX right alignment mode."]
    #[inline(always)]
    pub fn tx_left_align(&mut self) -> TX_LEFT_ALIGN_W<'_, TX_CONF_SPEC> {
        TX_LEFT_ALIGN_W::new(self, 15)
    }
    #[doc = "Bit 16 - 1: Sent 32 bits in 24 channel bits mode. 0: Sent 24 bits in 24 channel bits mode"]
    #[inline(always)]
    pub fn tx_24_fill_en(&mut self) -> TX_24_FILL_EN_W<'_, TX_CONF_SPEC> {
        TX_24_FILL_EN_W::new(self, 16)
    }
    #[doc = "Bit 17 - 0: WS should be 0 when sending left channel data, and WS is 1in right channel. 1: WS should be 1 when sending left channel data, and WS is 0in right channel."]
    #[inline(always)]
    pub fn tx_ws_idle_pol(&mut self) -> TX_WS_IDLE_POL_W<'_, TX_CONF_SPEC> {
        TX_WS_IDLE_POL_W::new(self, 17)
    }
    #[doc = "Bit 18 - I2S Tx bit endian. 1:small endian, the LSB is sent first. 0:big endian, the MSB is sent first."]
    #[inline(always)]
    pub fn tx_bit_order(&mut self) -> TX_BIT_ORDER_W<'_, TX_CONF_SPEC> {
        TX_BIT_ORDER_W::new(self, 18)
    }
    #[doc = "Bit 19 - 1: Enable I2S TDM Tx mode . 0: Disable."]
    #[inline(always)]
    pub fn tx_tdm_en(&mut self) -> TX_TDM_EN_W<'_, TX_CONF_SPEC> {
        TX_TDM_EN_W::new(self, 19)
    }
    #[doc = "Bit 20 - 1: Enable I2S PDM Tx mode . 0: Disable."]
    #[inline(always)]
    pub fn tx_pdm_en(&mut self) -> TX_PDM_EN_W<'_, TX_CONF_SPEC> {
        TX_PDM_EN_W::new(self, 20)
    }
    #[doc = "Bits 24:26 - I2S transmitter channel mode configuration bits."]
    #[inline(always)]
    pub fn tx_chan_mod(&mut self) -> TX_CHAN_MOD_W<'_, TX_CONF_SPEC> {
        TX_CHAN_MOD_W::new(self, 24)
    }
    #[doc = "Bit 27 - Enable signal loop back mode with transmitter module and receiver module sharing the same WS and BCK signals."]
    #[inline(always)]
    pub fn sig_loopback(&mut self) -> SIG_LOOPBACK_W<'_, TX_CONF_SPEC> {
        SIG_LOOPBACK_W::new(self, 27)
    }
}
#[doc = "I2S TX configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_CONF_SPEC;
impl crate::RegisterSpec for TX_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_conf::R`](R) reader structure"]
impl crate::Readable for TX_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_conf::W`](W) writer structure"]
impl crate::Writable for TX_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_CONF to value 0xb200"]
impl crate::Resettable for TX_CONF_SPEC {
    const RESET_VALUE: u32 = 0xb200;
}
