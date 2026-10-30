#[doc = "Register `RS485_CONF` reader"]
pub type R = crate::R<RS485_CONF_SPEC>;
#[doc = "Register `RS485_CONF` writer"]
pub type W = crate::W<RS485_CONF_SPEC>;
#[doc = "Field `RS485_EN` reader - Set this bit to choose the rs485 mode."]
pub type RS485_EN_R = crate::BitReader;
#[doc = "Field `RS485_EN` writer - Set this bit to choose the rs485 mode."]
pub type RS485_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DL0_EN` reader - Set this bit to delay the stop bit by 1 bit."]
pub type DL0_EN_R = crate::BitReader;
#[doc = "Field `DL0_EN` writer - Set this bit to delay the stop bit by 1 bit."]
pub type DL0_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DL1_EN` reader - Set this bit to delay the stop bit by 1 bit."]
pub type DL1_EN_R = crate::BitReader;
#[doc = "Field `DL1_EN` writer - Set this bit to delay the stop bit by 1 bit."]
pub type DL1_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RS485TX_RX_EN` reader - Set this bit to enable receiver could receive data when the transmitter is transmitting data in rs485 mode."]
pub type RS485TX_RX_EN_R = crate::BitReader;
#[doc = "Field `RS485TX_RX_EN` writer - Set this bit to enable receiver could receive data when the transmitter is transmitting data in rs485 mode."]
pub type RS485TX_RX_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RS485RXBY_TX_EN` reader - 1'h1: enable rs485 transmitter to send data when rs485 receiver line is busy."]
pub type RS485RXBY_TX_EN_R = crate::BitReader;
#[doc = "Field `RS485RXBY_TX_EN` writer - 1'h1: enable rs485 transmitter to send data when rs485 receiver line is busy."]
pub type RS485RXBY_TX_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RS485_RX_DLY_NUM` reader - This register is used to delay the receiver's internal data signal."]
pub type RS485_RX_DLY_NUM_R = crate::BitReader;
#[doc = "Field `RS485_RX_DLY_NUM` writer - This register is used to delay the receiver's internal data signal."]
pub type RS485_RX_DLY_NUM_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RS485_TX_DLY_NUM` reader - This register is used to delay the transmitter's internal data signal."]
pub type RS485_TX_DLY_NUM_R = crate::FieldReader;
#[doc = "Field `RS485_TX_DLY_NUM` writer - This register is used to delay the transmitter's internal data signal."]
pub type RS485_TX_DLY_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bit 0 - Set this bit to choose the rs485 mode."]
    #[inline(always)]
    pub fn rs485_en(&self) -> RS485_EN_R {
        RS485_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set this bit to delay the stop bit by 1 bit."]
    #[inline(always)]
    pub fn dl0_en(&self) -> DL0_EN_R {
        DL0_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set this bit to delay the stop bit by 1 bit."]
    #[inline(always)]
    pub fn dl1_en(&self) -> DL1_EN_R {
        DL1_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Set this bit to enable receiver could receive data when the transmitter is transmitting data in rs485 mode."]
    #[inline(always)]
    pub fn rs485tx_rx_en(&self) -> RS485TX_RX_EN_R {
        RS485TX_RX_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - 1'h1: enable rs485 transmitter to send data when rs485 receiver line is busy."]
    #[inline(always)]
    pub fn rs485rxby_tx_en(&self) -> RS485RXBY_TX_EN_R {
        RS485RXBY_TX_EN_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - This register is used to delay the receiver's internal data signal."]
    #[inline(always)]
    pub fn rs485_rx_dly_num(&self) -> RS485_RX_DLY_NUM_R {
        RS485_RX_DLY_NUM_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bits 6:9 - This register is used to delay the transmitter's internal data signal."]
    #[inline(always)]
    pub fn rs485_tx_dly_num(&self) -> RS485_TX_DLY_NUM_R {
        RS485_TX_DLY_NUM_R::new(((self.bits >> 6) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RS485_CONF")
            .field("rs485_en", &self.rs485_en())
            .field("dl0_en", &self.dl0_en())
            .field("dl1_en", &self.dl1_en())
            .field("rs485tx_rx_en", &self.rs485tx_rx_en())
            .field("rs485rxby_tx_en", &self.rs485rxby_tx_en())
            .field("rs485_rx_dly_num", &self.rs485_rx_dly_num())
            .field("rs485_tx_dly_num", &self.rs485_tx_dly_num())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit to choose the rs485 mode."]
    #[inline(always)]
    pub fn rs485_en(&mut self) -> RS485_EN_W<'_, RS485_CONF_SPEC> {
        RS485_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set this bit to delay the stop bit by 1 bit."]
    #[inline(always)]
    pub fn dl0_en(&mut self) -> DL0_EN_W<'_, RS485_CONF_SPEC> {
        DL0_EN_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set this bit to delay the stop bit by 1 bit."]
    #[inline(always)]
    pub fn dl1_en(&mut self) -> DL1_EN_W<'_, RS485_CONF_SPEC> {
        DL1_EN_W::new(self, 2)
    }
    #[doc = "Bit 3 - Set this bit to enable receiver could receive data when the transmitter is transmitting data in rs485 mode."]
    #[inline(always)]
    pub fn rs485tx_rx_en(&mut self) -> RS485TX_RX_EN_W<'_, RS485_CONF_SPEC> {
        RS485TX_RX_EN_W::new(self, 3)
    }
    #[doc = "Bit 4 - 1'h1: enable rs485 transmitter to send data when rs485 receiver line is busy."]
    #[inline(always)]
    pub fn rs485rxby_tx_en(&mut self) -> RS485RXBY_TX_EN_W<'_, RS485_CONF_SPEC> {
        RS485RXBY_TX_EN_W::new(self, 4)
    }
    #[doc = "Bit 5 - This register is used to delay the receiver's internal data signal."]
    #[inline(always)]
    pub fn rs485_rx_dly_num(&mut self) -> RS485_RX_DLY_NUM_W<'_, RS485_CONF_SPEC> {
        RS485_RX_DLY_NUM_W::new(self, 5)
    }
    #[doc = "Bits 6:9 - This register is used to delay the transmitter's internal data signal."]
    #[inline(always)]
    pub fn rs485_tx_dly_num(&mut self) -> RS485_TX_DLY_NUM_W<'_, RS485_CONF_SPEC> {
        RS485_TX_DLY_NUM_W::new(self, 6)
    }
}
#[doc = "RS485 mode configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`rs485_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rs485_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RS485_CONF_SPEC;
impl crate::RegisterSpec for RS485_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rs485_conf::R`](R) reader structure"]
impl crate::Readable for RS485_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rs485_conf::W`](W) writer structure"]
impl crate::Writable for RS485_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RS485_CONF to value 0"]
impl crate::Resettable for RS485_CONF_SPEC {}
