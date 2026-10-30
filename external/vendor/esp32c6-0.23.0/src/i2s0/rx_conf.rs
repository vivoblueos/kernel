#[doc = "Register `RX_CONF` reader"]
pub type R = crate::R<RX_CONF_SPEC>;
#[doc = "Register `RX_CONF` writer"]
pub type W = crate::W<RX_CONF_SPEC>;
#[doc = "Field `RX_RESET` writer - Set this bit to reset receiver"]
pub type RX_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_FIFO_RESET` writer - Set this bit to reset Rx AFIFO"]
pub type RX_FIFO_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_START` reader - Set this bit to start receiving data"]
pub type RX_START_R = crate::BitReader;
#[doc = "Field `RX_START` writer - Set this bit to start receiving data"]
pub type RX_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_SLAVE_MOD` reader - Set this bit to enable slave receiver mode"]
pub type RX_SLAVE_MOD_R = crate::BitReader;
#[doc = "Field `RX_SLAVE_MOD` writer - Set this bit to enable slave receiver mode"]
pub type RX_SLAVE_MOD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_MONO` reader - Set this bit to enable receiver in mono mode"]
pub type RX_MONO_R = crate::BitReader;
#[doc = "Field `RX_MONO` writer - Set this bit to enable receiver in mono mode"]
pub type RX_MONO_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_BIG_ENDIAN` reader - I2S Rx byte endian, 1: low addr value to high addr. 0: low addr with low addr value."]
pub type RX_BIG_ENDIAN_R = crate::BitReader;
#[doc = "Field `RX_BIG_ENDIAN` writer - I2S Rx byte endian, 1: low addr value to high addr. 0: low addr with low addr value."]
pub type RX_BIG_ENDIAN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_UPDATE` reader - Set 1 to update I2S RX registers from APB clock domain to I2S RX clock domain. This bit will be cleared by hardware after update register done."]
pub type RX_UPDATE_R = crate::BitReader;
#[doc = "Field `RX_UPDATE` writer - Set 1 to update I2S RX registers from APB clock domain to I2S RX clock domain. This bit will be cleared by hardware after update register done."]
pub type RX_UPDATE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_MONO_FST_VLD` reader - 1: The first channel data value is valid in I2S RX mono mode. 0: The second channel data value is valid in I2S RX mono mode."]
pub type RX_MONO_FST_VLD_R = crate::BitReader;
#[doc = "Field `RX_MONO_FST_VLD` writer - 1: The first channel data value is valid in I2S RX mono mode. 0: The second channel data value is valid in I2S RX mono mode."]
pub type RX_MONO_FST_VLD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_PCM_CONF` reader - I2S RX compress/decompress configuration bit. & 0 (atol): A-Law decompress, 1 (ltoa) : A-Law compress, 2 (utol) : u-Law decompress, 3 (ltou) : u-Law compress. &"]
pub type RX_PCM_CONF_R = crate::FieldReader;
#[doc = "Field `RX_PCM_CONF` writer - I2S RX compress/decompress configuration bit. & 0 (atol): A-Law decompress, 1 (ltoa) : A-Law compress, 2 (utol) : u-Law decompress, 3 (ltou) : u-Law compress. &"]
pub type RX_PCM_CONF_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `RX_PCM_BYPASS` reader - Set this bit to bypass Compress/Decompress module for received data."]
pub type RX_PCM_BYPASS_R = crate::BitReader;
#[doc = "Field `RX_PCM_BYPASS` writer - Set this bit to bypass Compress/Decompress module for received data."]
pub type RX_PCM_BYPASS_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_STOP_MODE` reader - 0 : I2S Rx only stop when reg_rx_start is cleared. 1: Stop when reg_rx_start is 0 or in_suc_eof is 1. 2: Stop I2S RX when reg_rx_start is 0 or RX FIFO is full."]
pub type RX_STOP_MODE_R = crate::FieldReader;
#[doc = "Field `RX_STOP_MODE` writer - 0 : I2S Rx only stop when reg_rx_start is cleared. 1: Stop when reg_rx_start is 0 or in_suc_eof is 1. 2: Stop I2S RX when reg_rx_start is 0 or RX FIFO is full."]
pub type RX_STOP_MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `RX_LEFT_ALIGN` reader - 1: I2S RX left alignment mode. 0: I2S RX right alignment mode."]
pub type RX_LEFT_ALIGN_R = crate::BitReader;
#[doc = "Field `RX_LEFT_ALIGN` writer - 1: I2S RX left alignment mode. 0: I2S RX right alignment mode."]
pub type RX_LEFT_ALIGN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_24_FILL_EN` reader - 1: store 24 channel bits to 32 bits. 0:store 24 channel bits to 24 bits."]
pub type RX_24_FILL_EN_R = crate::BitReader;
#[doc = "Field `RX_24_FILL_EN` writer - 1: store 24 channel bits to 32 bits. 0:store 24 channel bits to 24 bits."]
pub type RX_24_FILL_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_WS_IDLE_POL` reader - 0: WS should be 0 when receiving left channel data, and WS is 1in right channel. 1: WS should be 1 when receiving left channel data, and WS is 0in right channel."]
pub type RX_WS_IDLE_POL_R = crate::BitReader;
#[doc = "Field `RX_WS_IDLE_POL` writer - 0: WS should be 0 when receiving left channel data, and WS is 1in right channel. 1: WS should be 1 when receiving left channel data, and WS is 0in right channel."]
pub type RX_WS_IDLE_POL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_BIT_ORDER` reader - I2S Rx bit endian. 1:small endian, the LSB is received first. 0:big endian, the MSB is received first."]
pub type RX_BIT_ORDER_R = crate::BitReader;
#[doc = "Field `RX_BIT_ORDER` writer - I2S Rx bit endian. 1:small endian, the LSB is received first. 0:big endian, the MSB is received first."]
pub type RX_BIT_ORDER_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_TDM_EN` reader - 1: Enable I2S TDM Rx mode . 0: Disable."]
pub type RX_TDM_EN_R = crate::BitReader;
#[doc = "Field `RX_TDM_EN` writer - 1: Enable I2S TDM Rx mode . 0: Disable."]
pub type RX_TDM_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_PDM_EN` reader - 1: Enable I2S PDM Rx mode . 0: Disable."]
pub type RX_PDM_EN_R = crate::BitReader;
#[doc = "Field `RX_PDM_EN` writer - 1: Enable I2S PDM Rx mode . 0: Disable."]
pub type RX_PDM_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 2 - Set this bit to start receiving data"]
    #[inline(always)]
    pub fn rx_start(&self) -> RX_START_R {
        RX_START_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Set this bit to enable slave receiver mode"]
    #[inline(always)]
    pub fn rx_slave_mod(&self) -> RX_SLAVE_MOD_R {
        RX_SLAVE_MOD_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 5 - Set this bit to enable receiver in mono mode"]
    #[inline(always)]
    pub fn rx_mono(&self) -> RX_MONO_R {
        RX_MONO_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 7 - I2S Rx byte endian, 1: low addr value to high addr. 0: low addr with low addr value."]
    #[inline(always)]
    pub fn rx_big_endian(&self) -> RX_BIG_ENDIAN_R {
        RX_BIG_ENDIAN_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Set 1 to update I2S RX registers from APB clock domain to I2S RX clock domain. This bit will be cleared by hardware after update register done."]
    #[inline(always)]
    pub fn rx_update(&self) -> RX_UPDATE_R {
        RX_UPDATE_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - 1: The first channel data value is valid in I2S RX mono mode. 0: The second channel data value is valid in I2S RX mono mode."]
    #[inline(always)]
    pub fn rx_mono_fst_vld(&self) -> RX_MONO_FST_VLD_R {
        RX_MONO_FST_VLD_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bits 10:11 - I2S RX compress/decompress configuration bit. & 0 (atol): A-Law decompress, 1 (ltoa) : A-Law compress, 2 (utol) : u-Law decompress, 3 (ltou) : u-Law compress. &"]
    #[inline(always)]
    pub fn rx_pcm_conf(&self) -> RX_PCM_CONF_R {
        RX_PCM_CONF_R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bit 12 - Set this bit to bypass Compress/Decompress module for received data."]
    #[inline(always)]
    pub fn rx_pcm_bypass(&self) -> RX_PCM_BYPASS_R {
        RX_PCM_BYPASS_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bits 13:14 - 0 : I2S Rx only stop when reg_rx_start is cleared. 1: Stop when reg_rx_start is 0 or in_suc_eof is 1. 2: Stop I2S RX when reg_rx_start is 0 or RX FIFO is full."]
    #[inline(always)]
    pub fn rx_stop_mode(&self) -> RX_STOP_MODE_R {
        RX_STOP_MODE_R::new(((self.bits >> 13) & 3) as u8)
    }
    #[doc = "Bit 15 - 1: I2S RX left alignment mode. 0: I2S RX right alignment mode."]
    #[inline(always)]
    pub fn rx_left_align(&self) -> RX_LEFT_ALIGN_R {
        RX_LEFT_ALIGN_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - 1: store 24 channel bits to 32 bits. 0:store 24 channel bits to 24 bits."]
    #[inline(always)]
    pub fn rx_24_fill_en(&self) -> RX_24_FILL_EN_R {
        RX_24_FILL_EN_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - 0: WS should be 0 when receiving left channel data, and WS is 1in right channel. 1: WS should be 1 when receiving left channel data, and WS is 0in right channel."]
    #[inline(always)]
    pub fn rx_ws_idle_pol(&self) -> RX_WS_IDLE_POL_R {
        RX_WS_IDLE_POL_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - I2S Rx bit endian. 1:small endian, the LSB is received first. 0:big endian, the MSB is received first."]
    #[inline(always)]
    pub fn rx_bit_order(&self) -> RX_BIT_ORDER_R {
        RX_BIT_ORDER_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - 1: Enable I2S TDM Rx mode . 0: Disable."]
    #[inline(always)]
    pub fn rx_tdm_en(&self) -> RX_TDM_EN_R {
        RX_TDM_EN_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - 1: Enable I2S PDM Rx mode . 0: Disable."]
    #[inline(always)]
    pub fn rx_pdm_en(&self) -> RX_PDM_EN_R {
        RX_PDM_EN_R::new(((self.bits >> 20) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RX_CONF")
            .field("rx_start", &self.rx_start())
            .field("rx_slave_mod", &self.rx_slave_mod())
            .field("rx_mono", &self.rx_mono())
            .field("rx_big_endian", &self.rx_big_endian())
            .field("rx_update", &self.rx_update())
            .field("rx_mono_fst_vld", &self.rx_mono_fst_vld())
            .field("rx_pcm_conf", &self.rx_pcm_conf())
            .field("rx_pcm_bypass", &self.rx_pcm_bypass())
            .field("rx_stop_mode", &self.rx_stop_mode())
            .field("rx_left_align", &self.rx_left_align())
            .field("rx_24_fill_en", &self.rx_24_fill_en())
            .field("rx_ws_idle_pol", &self.rx_ws_idle_pol())
            .field("rx_bit_order", &self.rx_bit_order())
            .field("rx_tdm_en", &self.rx_tdm_en())
            .field("rx_pdm_en", &self.rx_pdm_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit to reset receiver"]
    #[inline(always)]
    pub fn rx_reset(&mut self) -> RX_RESET_W<'_, RX_CONF_SPEC> {
        RX_RESET_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set this bit to reset Rx AFIFO"]
    #[inline(always)]
    pub fn rx_fifo_reset(&mut self) -> RX_FIFO_RESET_W<'_, RX_CONF_SPEC> {
        RX_FIFO_RESET_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set this bit to start receiving data"]
    #[inline(always)]
    pub fn rx_start(&mut self) -> RX_START_W<'_, RX_CONF_SPEC> {
        RX_START_W::new(self, 2)
    }
    #[doc = "Bit 3 - Set this bit to enable slave receiver mode"]
    #[inline(always)]
    pub fn rx_slave_mod(&mut self) -> RX_SLAVE_MOD_W<'_, RX_CONF_SPEC> {
        RX_SLAVE_MOD_W::new(self, 3)
    }
    #[doc = "Bit 5 - Set this bit to enable receiver in mono mode"]
    #[inline(always)]
    pub fn rx_mono(&mut self) -> RX_MONO_W<'_, RX_CONF_SPEC> {
        RX_MONO_W::new(self, 5)
    }
    #[doc = "Bit 7 - I2S Rx byte endian, 1: low addr value to high addr. 0: low addr with low addr value."]
    #[inline(always)]
    pub fn rx_big_endian(&mut self) -> RX_BIG_ENDIAN_W<'_, RX_CONF_SPEC> {
        RX_BIG_ENDIAN_W::new(self, 7)
    }
    #[doc = "Bit 8 - Set 1 to update I2S RX registers from APB clock domain to I2S RX clock domain. This bit will be cleared by hardware after update register done."]
    #[inline(always)]
    pub fn rx_update(&mut self) -> RX_UPDATE_W<'_, RX_CONF_SPEC> {
        RX_UPDATE_W::new(self, 8)
    }
    #[doc = "Bit 9 - 1: The first channel data value is valid in I2S RX mono mode. 0: The second channel data value is valid in I2S RX mono mode."]
    #[inline(always)]
    pub fn rx_mono_fst_vld(&mut self) -> RX_MONO_FST_VLD_W<'_, RX_CONF_SPEC> {
        RX_MONO_FST_VLD_W::new(self, 9)
    }
    #[doc = "Bits 10:11 - I2S RX compress/decompress configuration bit. & 0 (atol): A-Law decompress, 1 (ltoa) : A-Law compress, 2 (utol) : u-Law decompress, 3 (ltou) : u-Law compress. &"]
    #[inline(always)]
    pub fn rx_pcm_conf(&mut self) -> RX_PCM_CONF_W<'_, RX_CONF_SPEC> {
        RX_PCM_CONF_W::new(self, 10)
    }
    #[doc = "Bit 12 - Set this bit to bypass Compress/Decompress module for received data."]
    #[inline(always)]
    pub fn rx_pcm_bypass(&mut self) -> RX_PCM_BYPASS_W<'_, RX_CONF_SPEC> {
        RX_PCM_BYPASS_W::new(self, 12)
    }
    #[doc = "Bits 13:14 - 0 : I2S Rx only stop when reg_rx_start is cleared. 1: Stop when reg_rx_start is 0 or in_suc_eof is 1. 2: Stop I2S RX when reg_rx_start is 0 or RX FIFO is full."]
    #[inline(always)]
    pub fn rx_stop_mode(&mut self) -> RX_STOP_MODE_W<'_, RX_CONF_SPEC> {
        RX_STOP_MODE_W::new(self, 13)
    }
    #[doc = "Bit 15 - 1: I2S RX left alignment mode. 0: I2S RX right alignment mode."]
    #[inline(always)]
    pub fn rx_left_align(&mut self) -> RX_LEFT_ALIGN_W<'_, RX_CONF_SPEC> {
        RX_LEFT_ALIGN_W::new(self, 15)
    }
    #[doc = "Bit 16 - 1: store 24 channel bits to 32 bits. 0:store 24 channel bits to 24 bits."]
    #[inline(always)]
    pub fn rx_24_fill_en(&mut self) -> RX_24_FILL_EN_W<'_, RX_CONF_SPEC> {
        RX_24_FILL_EN_W::new(self, 16)
    }
    #[doc = "Bit 17 - 0: WS should be 0 when receiving left channel data, and WS is 1in right channel. 1: WS should be 1 when receiving left channel data, and WS is 0in right channel."]
    #[inline(always)]
    pub fn rx_ws_idle_pol(&mut self) -> RX_WS_IDLE_POL_W<'_, RX_CONF_SPEC> {
        RX_WS_IDLE_POL_W::new(self, 17)
    }
    #[doc = "Bit 18 - I2S Rx bit endian. 1:small endian, the LSB is received first. 0:big endian, the MSB is received first."]
    #[inline(always)]
    pub fn rx_bit_order(&mut self) -> RX_BIT_ORDER_W<'_, RX_CONF_SPEC> {
        RX_BIT_ORDER_W::new(self, 18)
    }
    #[doc = "Bit 19 - 1: Enable I2S TDM Rx mode . 0: Disable."]
    #[inline(always)]
    pub fn rx_tdm_en(&mut self) -> RX_TDM_EN_W<'_, RX_CONF_SPEC> {
        RX_TDM_EN_W::new(self, 19)
    }
    #[doc = "Bit 20 - 1: Enable I2S PDM Rx mode . 0: Disable."]
    #[inline(always)]
    pub fn rx_pdm_en(&mut self) -> RX_PDM_EN_W<'_, RX_CONF_SPEC> {
        RX_PDM_EN_W::new(self, 20)
    }
}
#[doc = "I2S RX configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RX_CONF_SPEC;
impl crate::RegisterSpec for RX_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rx_conf::R`](R) reader structure"]
impl crate::Readable for RX_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rx_conf::W`](W) writer structure"]
impl crate::Writable for RX_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RX_CONF to value 0x9600"]
impl crate::Resettable for RX_CONF_SPEC {
    const RESET_VALUE: u32 = 0x9600;
}
