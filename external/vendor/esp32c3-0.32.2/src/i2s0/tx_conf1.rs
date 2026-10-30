#[doc = "Register `TX_CONF1` reader"]
pub type R = crate::R<TX_CONF1_SPEC>;
#[doc = "Register `TX_CONF1` writer"]
pub type W = crate::W<TX_CONF1_SPEC>;
#[doc = "Field `TX_TDM_WS_WIDTH` reader - The width of tx_ws_out in TDM mode is (I2S_TX_TDM_WS_WIDTH\\[6:0\\] +1) * T_bck"]
pub type TX_TDM_WS_WIDTH_R = crate::FieldReader;
#[doc = "Field `TX_TDM_WS_WIDTH` writer - The width of tx_ws_out in TDM mode is (I2S_TX_TDM_WS_WIDTH\\[6:0\\] +1) * T_bck"]
pub type TX_TDM_WS_WIDTH_W<'a, REG> = crate::FieldWriter<'a, REG, 7>;
#[doc = "Field `TX_BCK_DIV_NUM` reader - Bit clock configuration bits in transmitter mode."]
pub type TX_BCK_DIV_NUM_R = crate::FieldReader;
#[doc = "Field `TX_BCK_DIV_NUM` writer - Bit clock configuration bits in transmitter mode."]
pub type TX_BCK_DIV_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `TX_BITS_MOD` reader - Set the bits to configure the valid data bit length of I2S transmitter channel. 7: all the valid channel data is in 8-bit-mode. 15: all the valid channel data is in 16-bit-mode. 23: all the valid channel data is in 24-bit-mode. 31:all the valid channel data is in 32-bit-mode."]
pub type TX_BITS_MOD_R = crate::FieldReader;
#[doc = "Field `TX_BITS_MOD` writer - Set the bits to configure the valid data bit length of I2S transmitter channel. 7: all the valid channel data is in 8-bit-mode. 15: all the valid channel data is in 16-bit-mode. 23: all the valid channel data is in 24-bit-mode. 31:all the valid channel data is in 32-bit-mode."]
pub type TX_BITS_MOD_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `TX_HALF_SAMPLE_BITS` reader - I2S Tx half sample bits -1."]
pub type TX_HALF_SAMPLE_BITS_R = crate::FieldReader;
#[doc = "Field `TX_HALF_SAMPLE_BITS` writer - I2S Tx half sample bits -1."]
pub type TX_HALF_SAMPLE_BITS_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
#[doc = "Field `TX_TDM_CHAN_BITS` reader - The Tx bit number for each channel minus 1in TDM mode."]
pub type TX_TDM_CHAN_BITS_R = crate::FieldReader;
#[doc = "Field `TX_TDM_CHAN_BITS` writer - The Tx bit number for each channel minus 1in TDM mode."]
pub type TX_TDM_CHAN_BITS_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `TX_MSB_SHIFT` reader - Set this bit to enable transmitter in Phillips standard mode"]
pub type TX_MSB_SHIFT_R = crate::BitReader;
#[doc = "Field `TX_MSB_SHIFT` writer - Set this bit to enable transmitter in Phillips standard mode"]
pub type TX_MSB_SHIFT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TX_BCK_NO_DLY` reader - 1: BCK is not delayed to generate pos/neg edge in master mode. 0: BCK is delayed to generate pos/neg edge in master mode."]
pub type TX_BCK_NO_DLY_R = crate::BitReader;
#[doc = "Field `TX_BCK_NO_DLY` writer - 1: BCK is not delayed to generate pos/neg edge in master mode. 0: BCK is delayed to generate pos/neg edge in master mode."]
pub type TX_BCK_NO_DLY_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:6 - The width of tx_ws_out in TDM mode is (I2S_TX_TDM_WS_WIDTH\\[6:0\\] +1) * T_bck"]
    #[inline(always)]
    pub fn tx_tdm_ws_width(&self) -> TX_TDM_WS_WIDTH_R {
        TX_TDM_WS_WIDTH_R::new((self.bits & 0x7f) as u8)
    }
    #[doc = "Bits 7:12 - Bit clock configuration bits in transmitter mode."]
    #[inline(always)]
    pub fn tx_bck_div_num(&self) -> TX_BCK_DIV_NUM_R {
        TX_BCK_DIV_NUM_R::new(((self.bits >> 7) & 0x3f) as u8)
    }
    #[doc = "Bits 13:17 - Set the bits to configure the valid data bit length of I2S transmitter channel. 7: all the valid channel data is in 8-bit-mode. 15: all the valid channel data is in 16-bit-mode. 23: all the valid channel data is in 24-bit-mode. 31:all the valid channel data is in 32-bit-mode."]
    #[inline(always)]
    pub fn tx_bits_mod(&self) -> TX_BITS_MOD_R {
        TX_BITS_MOD_R::new(((self.bits >> 13) & 0x1f) as u8)
    }
    #[doc = "Bits 18:23 - I2S Tx half sample bits -1."]
    #[inline(always)]
    pub fn tx_half_sample_bits(&self) -> TX_HALF_SAMPLE_BITS_R {
        TX_HALF_SAMPLE_BITS_R::new(((self.bits >> 18) & 0x3f) as u8)
    }
    #[doc = "Bits 24:28 - The Tx bit number for each channel minus 1in TDM mode."]
    #[inline(always)]
    pub fn tx_tdm_chan_bits(&self) -> TX_TDM_CHAN_BITS_R {
        TX_TDM_CHAN_BITS_R::new(((self.bits >> 24) & 0x1f) as u8)
    }
    #[doc = "Bit 29 - Set this bit to enable transmitter in Phillips standard mode"]
    #[inline(always)]
    pub fn tx_msb_shift(&self) -> TX_MSB_SHIFT_R {
        TX_MSB_SHIFT_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - 1: BCK is not delayed to generate pos/neg edge in master mode. 0: BCK is delayed to generate pos/neg edge in master mode."]
    #[inline(always)]
    pub fn tx_bck_no_dly(&self) -> TX_BCK_NO_DLY_R {
        TX_BCK_NO_DLY_R::new(((self.bits >> 30) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_CONF1")
            .field("tx_tdm_ws_width", &self.tx_tdm_ws_width())
            .field("tx_bck_div_num", &self.tx_bck_div_num())
            .field("tx_bits_mod", &self.tx_bits_mod())
            .field("tx_half_sample_bits", &self.tx_half_sample_bits())
            .field("tx_tdm_chan_bits", &self.tx_tdm_chan_bits())
            .field("tx_msb_shift", &self.tx_msb_shift())
            .field("tx_bck_no_dly", &self.tx_bck_no_dly())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:6 - The width of tx_ws_out in TDM mode is (I2S_TX_TDM_WS_WIDTH\\[6:0\\] +1) * T_bck"]
    #[inline(always)]
    pub fn tx_tdm_ws_width(&mut self) -> TX_TDM_WS_WIDTH_W<'_, TX_CONF1_SPEC> {
        TX_TDM_WS_WIDTH_W::new(self, 0)
    }
    #[doc = "Bits 7:12 - Bit clock configuration bits in transmitter mode."]
    #[inline(always)]
    pub fn tx_bck_div_num(&mut self) -> TX_BCK_DIV_NUM_W<'_, TX_CONF1_SPEC> {
        TX_BCK_DIV_NUM_W::new(self, 7)
    }
    #[doc = "Bits 13:17 - Set the bits to configure the valid data bit length of I2S transmitter channel. 7: all the valid channel data is in 8-bit-mode. 15: all the valid channel data is in 16-bit-mode. 23: all the valid channel data is in 24-bit-mode. 31:all the valid channel data is in 32-bit-mode."]
    #[inline(always)]
    pub fn tx_bits_mod(&mut self) -> TX_BITS_MOD_W<'_, TX_CONF1_SPEC> {
        TX_BITS_MOD_W::new(self, 13)
    }
    #[doc = "Bits 18:23 - I2S Tx half sample bits -1."]
    #[inline(always)]
    pub fn tx_half_sample_bits(&mut self) -> TX_HALF_SAMPLE_BITS_W<'_, TX_CONF1_SPEC> {
        TX_HALF_SAMPLE_BITS_W::new(self, 18)
    }
    #[doc = "Bits 24:28 - The Tx bit number for each channel minus 1in TDM mode."]
    #[inline(always)]
    pub fn tx_tdm_chan_bits(&mut self) -> TX_TDM_CHAN_BITS_W<'_, TX_CONF1_SPEC> {
        TX_TDM_CHAN_BITS_W::new(self, 24)
    }
    #[doc = "Bit 29 - Set this bit to enable transmitter in Phillips standard mode"]
    #[inline(always)]
    pub fn tx_msb_shift(&mut self) -> TX_MSB_SHIFT_W<'_, TX_CONF1_SPEC> {
        TX_MSB_SHIFT_W::new(self, 29)
    }
    #[doc = "Bit 30 - 1: BCK is not delayed to generate pos/neg edge in master mode. 0: BCK is delayed to generate pos/neg edge in master mode."]
    #[inline(always)]
    pub fn tx_bck_no_dly(&mut self) -> TX_BCK_NO_DLY_W<'_, TX_CONF1_SPEC> {
        TX_BCK_NO_DLY_W::new(self, 30)
    }
}
#[doc = "I2S TX configure register 1\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_conf1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_conf1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_CONF1_SPEC;
impl crate::RegisterSpec for TX_CONF1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_conf1::R`](R) reader structure"]
impl crate::Readable for TX_CONF1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_conf1::W`](W) writer structure"]
impl crate::Writable for TX_CONF1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_CONF1 to value 0x6f3d_e300"]
impl crate::Resettable for TX_CONF1_SPEC {
    const RESET_VALUE: u32 = 0x6f3d_e300;
}
