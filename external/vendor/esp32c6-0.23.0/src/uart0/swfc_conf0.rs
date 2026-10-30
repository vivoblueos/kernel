#[doc = "Register `SWFC_CONF0` reader"]
pub type R = crate::R<SWFC_CONF0_SPEC>;
#[doc = "Register `SWFC_CONF0` writer"]
pub type W = crate::W<SWFC_CONF0_SPEC>;
#[doc = "Field `XON_CHAR` reader - This register stores the Xon flow control char."]
pub type XON_CHAR_R = crate::FieldReader;
#[doc = "Field `XON_CHAR` writer - This register stores the Xon flow control char."]
pub type XON_CHAR_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `XOFF_CHAR` reader - This register stores the Xoff flow control char."]
pub type XOFF_CHAR_R = crate::FieldReader;
#[doc = "Field `XOFF_CHAR` writer - This register stores the Xoff flow control char."]
pub type XOFF_CHAR_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `XON_XOFF_STILL_SEND` reader - In software flow control mode, UART Tx is disabled once UART Rx receives XOFF. In this status, UART Tx can not transmit XOFF even the received data number is larger than UART_XOFF_THRESHOLD. Set this bit to enable UART Tx can transmit XON/XOFF when UART Tx is disabled."]
pub type XON_XOFF_STILL_SEND_R = crate::BitReader;
#[doc = "Field `XON_XOFF_STILL_SEND` writer - In software flow control mode, UART Tx is disabled once UART Rx receives XOFF. In this status, UART Tx can not transmit XOFF even the received data number is larger than UART_XOFF_THRESHOLD. Set this bit to enable UART Tx can transmit XON/XOFF when UART Tx is disabled."]
pub type XON_XOFF_STILL_SEND_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SW_FLOW_CON_EN` reader - Set this bit to enable software flow control. It is used with register sw_xon or sw_xoff."]
pub type SW_FLOW_CON_EN_R = crate::BitReader;
#[doc = "Field `SW_FLOW_CON_EN` writer - Set this bit to enable software flow control. It is used with register sw_xon or sw_xoff."]
pub type SW_FLOW_CON_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `XONOFF_DEL` reader - Set this bit to remove flow control char from the received data."]
pub type XONOFF_DEL_R = crate::BitReader;
#[doc = "Field `XONOFF_DEL` writer - Set this bit to remove flow control char from the received data."]
pub type XONOFF_DEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FORCE_XON` reader - Set this bit to enable the transmitter to go on sending data."]
pub type FORCE_XON_R = crate::BitReader;
#[doc = "Field `FORCE_XON` writer - Set this bit to enable the transmitter to go on sending data."]
pub type FORCE_XON_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FORCE_XOFF` reader - Set this bit to stop the transmitter from sending data."]
pub type FORCE_XOFF_R = crate::BitReader;
#[doc = "Field `FORCE_XOFF` writer - Set this bit to stop the transmitter from sending data."]
pub type FORCE_XOFF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SEND_XON` reader - Set this bit to send Xon char. It is cleared by hardware automatically."]
pub type SEND_XON_R = crate::BitReader;
#[doc = "Field `SEND_XON` writer - Set this bit to send Xon char. It is cleared by hardware automatically."]
pub type SEND_XON_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SEND_XOFF` reader - Set this bit to send Xoff char. It is cleared by hardware automatically."]
pub type SEND_XOFF_R = crate::BitReader;
#[doc = "Field `SEND_XOFF` writer - Set this bit to send Xoff char. It is cleared by hardware automatically."]
pub type SEND_XOFF_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:7 - This register stores the Xon flow control char."]
    #[inline(always)]
    pub fn xon_char(&self) -> XON_CHAR_R {
        XON_CHAR_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - This register stores the Xoff flow control char."]
    #[inline(always)]
    pub fn xoff_char(&self) -> XOFF_CHAR_R {
        XOFF_CHAR_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bit 16 - In software flow control mode, UART Tx is disabled once UART Rx receives XOFF. In this status, UART Tx can not transmit XOFF even the received data number is larger than UART_XOFF_THRESHOLD. Set this bit to enable UART Tx can transmit XON/XOFF when UART Tx is disabled."]
    #[inline(always)]
    pub fn xon_xoff_still_send(&self) -> XON_XOFF_STILL_SEND_R {
        XON_XOFF_STILL_SEND_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Set this bit to enable software flow control. It is used with register sw_xon or sw_xoff."]
    #[inline(always)]
    pub fn sw_flow_con_en(&self) -> SW_FLOW_CON_EN_R {
        SW_FLOW_CON_EN_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Set this bit to remove flow control char from the received data."]
    #[inline(always)]
    pub fn xonoff_del(&self) -> XONOFF_DEL_R {
        XONOFF_DEL_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Set this bit to enable the transmitter to go on sending data."]
    #[inline(always)]
    pub fn force_xon(&self) -> FORCE_XON_R {
        FORCE_XON_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Set this bit to stop the transmitter from sending data."]
    #[inline(always)]
    pub fn force_xoff(&self) -> FORCE_XOFF_R {
        FORCE_XOFF_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Set this bit to send Xon char. It is cleared by hardware automatically."]
    #[inline(always)]
    pub fn send_xon(&self) -> SEND_XON_R {
        SEND_XON_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - Set this bit to send Xoff char. It is cleared by hardware automatically."]
    #[inline(always)]
    pub fn send_xoff(&self) -> SEND_XOFF_R {
        SEND_XOFF_R::new(((self.bits >> 22) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SWFC_CONF0")
            .field("xon_char", &self.xon_char())
            .field("xoff_char", &self.xoff_char())
            .field("xon_xoff_still_send", &self.xon_xoff_still_send())
            .field("sw_flow_con_en", &self.sw_flow_con_en())
            .field("xonoff_del", &self.xonoff_del())
            .field("force_xon", &self.force_xon())
            .field("force_xoff", &self.force_xoff())
            .field("send_xon", &self.send_xon())
            .field("send_xoff", &self.send_xoff())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - This register stores the Xon flow control char."]
    #[inline(always)]
    pub fn xon_char(&mut self) -> XON_CHAR_W<'_, SWFC_CONF0_SPEC> {
        XON_CHAR_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - This register stores the Xoff flow control char."]
    #[inline(always)]
    pub fn xoff_char(&mut self) -> XOFF_CHAR_W<'_, SWFC_CONF0_SPEC> {
        XOFF_CHAR_W::new(self, 8)
    }
    #[doc = "Bit 16 - In software flow control mode, UART Tx is disabled once UART Rx receives XOFF. In this status, UART Tx can not transmit XOFF even the received data number is larger than UART_XOFF_THRESHOLD. Set this bit to enable UART Tx can transmit XON/XOFF when UART Tx is disabled."]
    #[inline(always)]
    pub fn xon_xoff_still_send(&mut self) -> XON_XOFF_STILL_SEND_W<'_, SWFC_CONF0_SPEC> {
        XON_XOFF_STILL_SEND_W::new(self, 16)
    }
    #[doc = "Bit 17 - Set this bit to enable software flow control. It is used with register sw_xon or sw_xoff."]
    #[inline(always)]
    pub fn sw_flow_con_en(&mut self) -> SW_FLOW_CON_EN_W<'_, SWFC_CONF0_SPEC> {
        SW_FLOW_CON_EN_W::new(self, 17)
    }
    #[doc = "Bit 18 - Set this bit to remove flow control char from the received data."]
    #[inline(always)]
    pub fn xonoff_del(&mut self) -> XONOFF_DEL_W<'_, SWFC_CONF0_SPEC> {
        XONOFF_DEL_W::new(self, 18)
    }
    #[doc = "Bit 19 - Set this bit to enable the transmitter to go on sending data."]
    #[inline(always)]
    pub fn force_xon(&mut self) -> FORCE_XON_W<'_, SWFC_CONF0_SPEC> {
        FORCE_XON_W::new(self, 19)
    }
    #[doc = "Bit 20 - Set this bit to stop the transmitter from sending data."]
    #[inline(always)]
    pub fn force_xoff(&mut self) -> FORCE_XOFF_W<'_, SWFC_CONF0_SPEC> {
        FORCE_XOFF_W::new(self, 20)
    }
    #[doc = "Bit 21 - Set this bit to send Xon char. It is cleared by hardware automatically."]
    #[inline(always)]
    pub fn send_xon(&mut self) -> SEND_XON_W<'_, SWFC_CONF0_SPEC> {
        SEND_XON_W::new(self, 21)
    }
    #[doc = "Bit 22 - Set this bit to send Xoff char. It is cleared by hardware automatically."]
    #[inline(always)]
    pub fn send_xoff(&mut self) -> SEND_XOFF_W<'_, SWFC_CONF0_SPEC> {
        SEND_XOFF_W::new(self, 22)
    }
}
#[doc = "Software flow-control character configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`swfc_conf0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`swfc_conf0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SWFC_CONF0_SPEC;
impl crate::RegisterSpec for SWFC_CONF0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`swfc_conf0::R`](R) reader structure"]
impl crate::Readable for SWFC_CONF0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`swfc_conf0::W`](W) writer structure"]
impl crate::Writable for SWFC_CONF0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SWFC_CONF0 to value 0x1311"]
impl crate::Resettable for SWFC_CONF0_SPEC {
    const RESET_VALUE: u32 = 0x1311;
}
