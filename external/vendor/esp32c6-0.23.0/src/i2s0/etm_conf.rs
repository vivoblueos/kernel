#[doc = "Register `ETM_CONF` reader"]
pub type R = crate::R<ETM_CONF_SPEC>;
#[doc = "Register `ETM_CONF` writer"]
pub type W = crate::W<ETM_CONF_SPEC>;
#[doc = "Field `ETM_TX_SEND_WORD_NUM` reader - I2S ETM send x words event. When sending word number of reg_etm_tx_send_word_num\\[9:0\\], i2s will trigger an etm event."]
pub type ETM_TX_SEND_WORD_NUM_R = crate::FieldReader<u16>;
#[doc = "Field `ETM_TX_SEND_WORD_NUM` writer - I2S ETM send x words event. When sending word number of reg_etm_tx_send_word_num\\[9:0\\], i2s will trigger an etm event."]
pub type ETM_TX_SEND_WORD_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `ETM_RX_RECEIVE_WORD_NUM` reader - I2S ETM receive x words event. When receiving word number of reg_etm_rx_receive_word_num\\[9:0\\], i2s will trigger an etm event."]
pub type ETM_RX_RECEIVE_WORD_NUM_R = crate::FieldReader<u16>;
#[doc = "Field `ETM_RX_RECEIVE_WORD_NUM` writer - I2S ETM receive x words event. When receiving word number of reg_etm_rx_receive_word_num\\[9:0\\], i2s will trigger an etm event."]
pub type ETM_RX_RECEIVE_WORD_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
impl R {
    #[doc = "Bits 0:9 - I2S ETM send x words event. When sending word number of reg_etm_tx_send_word_num\\[9:0\\], i2s will trigger an etm event."]
    #[inline(always)]
    pub fn etm_tx_send_word_num(&self) -> ETM_TX_SEND_WORD_NUM_R {
        ETM_TX_SEND_WORD_NUM_R::new((self.bits & 0x03ff) as u16)
    }
    #[doc = "Bits 10:19 - I2S ETM receive x words event. When receiving word number of reg_etm_rx_receive_word_num\\[9:0\\], i2s will trigger an etm event."]
    #[inline(always)]
    pub fn etm_rx_receive_word_num(&self) -> ETM_RX_RECEIVE_WORD_NUM_R {
        ETM_RX_RECEIVE_WORD_NUM_R::new(((self.bits >> 10) & 0x03ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ETM_CONF")
            .field("etm_tx_send_word_num", &self.etm_tx_send_word_num())
            .field("etm_rx_receive_word_num", &self.etm_rx_receive_word_num())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:9 - I2S ETM send x words event. When sending word number of reg_etm_tx_send_word_num\\[9:0\\], i2s will trigger an etm event."]
    #[inline(always)]
    pub fn etm_tx_send_word_num(&mut self) -> ETM_TX_SEND_WORD_NUM_W<'_, ETM_CONF_SPEC> {
        ETM_TX_SEND_WORD_NUM_W::new(self, 0)
    }
    #[doc = "Bits 10:19 - I2S ETM receive x words event. When receiving word number of reg_etm_rx_receive_word_num\\[9:0\\], i2s will trigger an etm event."]
    #[inline(always)]
    pub fn etm_rx_receive_word_num(&mut self) -> ETM_RX_RECEIVE_WORD_NUM_W<'_, ETM_CONF_SPEC> {
        ETM_RX_RECEIVE_WORD_NUM_W::new(self, 10)
    }
}
#[doc = "I2S ETM configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`etm_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`etm_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ETM_CONF_SPEC;
impl crate::RegisterSpec for ETM_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`etm_conf::R`](R) reader structure"]
impl crate::Readable for ETM_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`etm_conf::W`](W) writer structure"]
impl crate::Writable for ETM_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ETM_CONF to value 0x0001_0040"]
impl crate::Resettable for ETM_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0001_0040;
}
