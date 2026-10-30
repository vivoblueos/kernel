#[doc = "Register `INT_CLR` writer"]
pub type W = crate::W<INT_CLR_SPEC>;
#[doc = "Field `JTAG_IN_FLUSH` writer - Set this bit to clear the USB_DEVICE_JTAG_IN_FLUSH_INT interrupt."]
pub type JTAG_IN_FLUSH_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SOF` writer - Set this bit to clear the USB_DEVICE_JTAG_SOF_INT interrupt."]
pub type SOF_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SERIAL_OUT_RECV_PKT` writer - Set this bit to clear the USB_DEVICE_SERIAL_OUT_RECV_PKT_INT interrupt."]
pub type SERIAL_OUT_RECV_PKT_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SERIAL_IN_EMPTY` writer - Set this bit to clear the USB_DEVICE_SERIAL_IN_EMPTY_INT interrupt."]
pub type SERIAL_IN_EMPTY_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `PID_ERR` writer - Set this bit to clear the USB_DEVICE_PID_ERR_INT interrupt."]
pub type PID_ERR_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `CRC5_ERR` writer - Set this bit to clear the USB_DEVICE_CRC5_ERR_INT interrupt."]
pub type CRC5_ERR_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `CRC16_ERR` writer - Set this bit to clear the USB_DEVICE_CRC16_ERR_INT interrupt."]
pub type CRC16_ERR_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `STUFF_ERR` writer - Set this bit to clear the USB_DEVICE_STUFF_ERR_INT interrupt."]
pub type STUFF_ERR_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `IN_TOKEN_REC_IN_EP1` writer - Set this bit to clear the USB_DEVICE_IN_TOKEN_IN_EP1_INT interrupt."]
pub type IN_TOKEN_REC_IN_EP1_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `USB_BUS_RESET` writer - Set this bit to clear the USB_DEVICE_USB_BUS_RESET_INT interrupt."]
pub type USB_BUS_RESET_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `OUT_EP1_ZERO_PAYLOAD` writer - Set this bit to clear the USB_DEVICE_OUT_EP1_ZERO_PAYLOAD_INT interrupt."]
pub type OUT_EP1_ZERO_PAYLOAD_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `OUT_EP2_ZERO_PAYLOAD` writer - Set this bit to clear the USB_DEVICE_OUT_EP2_ZERO_PAYLOAD_INT interrupt."]
pub type OUT_EP2_ZERO_PAYLOAD_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `RTS_CHG` writer - Set this bit to clear the USB_DEVICE_RTS_CHG_INT interrupt."]
pub type RTS_CHG_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `DTR_CHG` writer - Set this bit to clear the USB_DEVICE_DTR_CHG_INT interrupt."]
pub type DTR_CHG_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `GET_LINE_CODE` writer - Set this bit to clear the USB_DEVICE_GET_LINE_CODE_INT interrupt."]
pub type GET_LINE_CODE_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SET_LINE_CODE` writer - Set this bit to clear the USB_DEVICE_SET_LINE_CODE_INT interrupt."]
pub type SET_LINE_CODE_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<INT_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit to clear the USB_DEVICE_JTAG_IN_FLUSH_INT interrupt."]
    #[inline(always)]
    pub fn jtag_in_flush(&mut self) -> JTAG_IN_FLUSH_W<'_, INT_CLR_SPEC> {
        JTAG_IN_FLUSH_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set this bit to clear the USB_DEVICE_JTAG_SOF_INT interrupt."]
    #[inline(always)]
    pub fn sof(&mut self) -> SOF_W<'_, INT_CLR_SPEC> {
        SOF_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set this bit to clear the USB_DEVICE_SERIAL_OUT_RECV_PKT_INT interrupt."]
    #[inline(always)]
    pub fn serial_out_recv_pkt(&mut self) -> SERIAL_OUT_RECV_PKT_W<'_, INT_CLR_SPEC> {
        SERIAL_OUT_RECV_PKT_W::new(self, 2)
    }
    #[doc = "Bit 3 - Set this bit to clear the USB_DEVICE_SERIAL_IN_EMPTY_INT interrupt."]
    #[inline(always)]
    pub fn serial_in_empty(&mut self) -> SERIAL_IN_EMPTY_W<'_, INT_CLR_SPEC> {
        SERIAL_IN_EMPTY_W::new(self, 3)
    }
    #[doc = "Bit 4 - Set this bit to clear the USB_DEVICE_PID_ERR_INT interrupt."]
    #[inline(always)]
    pub fn pid_err(&mut self) -> PID_ERR_W<'_, INT_CLR_SPEC> {
        PID_ERR_W::new(self, 4)
    }
    #[doc = "Bit 5 - Set this bit to clear the USB_DEVICE_CRC5_ERR_INT interrupt."]
    #[inline(always)]
    pub fn crc5_err(&mut self) -> CRC5_ERR_W<'_, INT_CLR_SPEC> {
        CRC5_ERR_W::new(self, 5)
    }
    #[doc = "Bit 6 - Set this bit to clear the USB_DEVICE_CRC16_ERR_INT interrupt."]
    #[inline(always)]
    pub fn crc16_err(&mut self) -> CRC16_ERR_W<'_, INT_CLR_SPEC> {
        CRC16_ERR_W::new(self, 6)
    }
    #[doc = "Bit 7 - Set this bit to clear the USB_DEVICE_STUFF_ERR_INT interrupt."]
    #[inline(always)]
    pub fn stuff_err(&mut self) -> STUFF_ERR_W<'_, INT_CLR_SPEC> {
        STUFF_ERR_W::new(self, 7)
    }
    #[doc = "Bit 8 - Set this bit to clear the USB_DEVICE_IN_TOKEN_IN_EP1_INT interrupt."]
    #[inline(always)]
    pub fn in_token_rec_in_ep1(&mut self) -> IN_TOKEN_REC_IN_EP1_W<'_, INT_CLR_SPEC> {
        IN_TOKEN_REC_IN_EP1_W::new(self, 8)
    }
    #[doc = "Bit 9 - Set this bit to clear the USB_DEVICE_USB_BUS_RESET_INT interrupt."]
    #[inline(always)]
    pub fn usb_bus_reset(&mut self) -> USB_BUS_RESET_W<'_, INT_CLR_SPEC> {
        USB_BUS_RESET_W::new(self, 9)
    }
    #[doc = "Bit 10 - Set this bit to clear the USB_DEVICE_OUT_EP1_ZERO_PAYLOAD_INT interrupt."]
    #[inline(always)]
    pub fn out_ep1_zero_payload(&mut self) -> OUT_EP1_ZERO_PAYLOAD_W<'_, INT_CLR_SPEC> {
        OUT_EP1_ZERO_PAYLOAD_W::new(self, 10)
    }
    #[doc = "Bit 11 - Set this bit to clear the USB_DEVICE_OUT_EP2_ZERO_PAYLOAD_INT interrupt."]
    #[inline(always)]
    pub fn out_ep2_zero_payload(&mut self) -> OUT_EP2_ZERO_PAYLOAD_W<'_, INT_CLR_SPEC> {
        OUT_EP2_ZERO_PAYLOAD_W::new(self, 11)
    }
    #[doc = "Bit 12 - Set this bit to clear the USB_DEVICE_RTS_CHG_INT interrupt."]
    #[inline(always)]
    pub fn rts_chg(&mut self) -> RTS_CHG_W<'_, INT_CLR_SPEC> {
        RTS_CHG_W::new(self, 12)
    }
    #[doc = "Bit 13 - Set this bit to clear the USB_DEVICE_DTR_CHG_INT interrupt."]
    #[inline(always)]
    pub fn dtr_chg(&mut self) -> DTR_CHG_W<'_, INT_CLR_SPEC> {
        DTR_CHG_W::new(self, 13)
    }
    #[doc = "Bit 14 - Set this bit to clear the USB_DEVICE_GET_LINE_CODE_INT interrupt."]
    #[inline(always)]
    pub fn get_line_code(&mut self) -> GET_LINE_CODE_W<'_, INT_CLR_SPEC> {
        GET_LINE_CODE_W::new(self, 14)
    }
    #[doc = "Bit 15 - Set this bit to clear the USB_DEVICE_SET_LINE_CODE_INT interrupt."]
    #[inline(always)]
    pub fn set_line_code(&mut self) -> SET_LINE_CODE_W<'_, INT_CLR_SPEC> {
        SET_LINE_CODE_W::new(self, 15)
    }
}
#[doc = "Interrupt clear status register.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_CLR_SPEC;
impl crate::RegisterSpec for INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`int_clr::W`](W) writer structure"]
impl crate::Writable for INT_CLR_SPEC {
    type Safety = crate::Unsafe;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0xffff;
}
#[doc = "`reset()` method sets INT_CLR to value 0"]
impl crate::Resettable for INT_CLR_SPEC {}
