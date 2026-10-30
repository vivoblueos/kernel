#[doc = "Register `INT_ST` reader"]
pub type R = crate::R<INT_ST_SPEC>;
#[doc = "Field `JTAG_IN_FLUSH` reader - The raw interrupt status bit for the USB_DEVICE_JTAG_IN_FLUSH_INT interrupt."]
pub type JTAG_IN_FLUSH_R = crate::BitReader;
#[doc = "Field `SOF` reader - The raw interrupt status bit for the USB_DEVICE_SOF_INT interrupt."]
pub type SOF_R = crate::BitReader;
#[doc = "Field `SERIAL_OUT_RECV_PKT` reader - The raw interrupt status bit for the USB_DEVICE_SERIAL_OUT_RECV_PKT_INT interrupt."]
pub type SERIAL_OUT_RECV_PKT_R = crate::BitReader;
#[doc = "Field `SERIAL_IN_EMPTY` reader - The raw interrupt status bit for the USB_DEVICE_SERIAL_IN_EMPTY_INT interrupt."]
pub type SERIAL_IN_EMPTY_R = crate::BitReader;
#[doc = "Field `PID_ERR` reader - The raw interrupt status bit for the USB_DEVICE_PID_ERR_INT interrupt."]
pub type PID_ERR_R = crate::BitReader;
#[doc = "Field `CRC5_ERR` reader - The raw interrupt status bit for the USB_DEVICE_CRC5_ERR_INT interrupt."]
pub type CRC5_ERR_R = crate::BitReader;
#[doc = "Field `CRC16_ERR` reader - The raw interrupt status bit for the USB_DEVICE_CRC16_ERR_INT interrupt."]
pub type CRC16_ERR_R = crate::BitReader;
#[doc = "Field `STUFF_ERR` reader - The raw interrupt status bit for the USB_DEVICE_STUFF_ERR_INT interrupt."]
pub type STUFF_ERR_R = crate::BitReader;
#[doc = "Field `IN_TOKEN_REC_IN_EP1` reader - The raw interrupt status bit for the USB_DEVICE_IN_TOKEN_REC_IN_EP1_INT interrupt."]
pub type IN_TOKEN_REC_IN_EP1_R = crate::BitReader;
#[doc = "Field `USB_BUS_RESET` reader - The raw interrupt status bit for the USB_DEVICE_USB_BUS_RESET_INT interrupt."]
pub type USB_BUS_RESET_R = crate::BitReader;
#[doc = "Field `OUT_EP1_ZERO_PAYLOAD` reader - The raw interrupt status bit for the USB_DEVICE_OUT_EP1_ZERO_PAYLOAD_INT interrupt."]
pub type OUT_EP1_ZERO_PAYLOAD_R = crate::BitReader;
#[doc = "Field `OUT_EP2_ZERO_PAYLOAD` reader - The raw interrupt status bit for the USB_DEVICE_OUT_EP2_ZERO_PAYLOAD_INT interrupt."]
pub type OUT_EP2_ZERO_PAYLOAD_R = crate::BitReader;
#[doc = "Field `RTS_CHG` reader - The raw interrupt status bit for the USB_DEVICE_RTS_CHG_INT interrupt."]
pub type RTS_CHG_R = crate::BitReader;
#[doc = "Field `DTR_CHG` reader - The raw interrupt status bit for the USB_DEVICE_DTR_CHG_INT interrupt."]
pub type DTR_CHG_R = crate::BitReader;
#[doc = "Field `GET_LINE_CODE` reader - The raw interrupt status bit for the USB_DEVICE_GET_LINE_CODE_INT interrupt."]
pub type GET_LINE_CODE_R = crate::BitReader;
#[doc = "Field `SET_LINE_CODE` reader - The raw interrupt status bit for the USB_DEVICE_SET_LINE_CODE_INT interrupt."]
pub type SET_LINE_CODE_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The raw interrupt status bit for the USB_DEVICE_JTAG_IN_FLUSH_INT interrupt."]
    #[inline(always)]
    pub fn jtag_in_flush(&self) -> JTAG_IN_FLUSH_R {
        JTAG_IN_FLUSH_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The raw interrupt status bit for the USB_DEVICE_SOF_INT interrupt."]
    #[inline(always)]
    pub fn sof(&self) -> SOF_R {
        SOF_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The raw interrupt status bit for the USB_DEVICE_SERIAL_OUT_RECV_PKT_INT interrupt."]
    #[inline(always)]
    pub fn serial_out_recv_pkt(&self) -> SERIAL_OUT_RECV_PKT_R {
        SERIAL_OUT_RECV_PKT_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The raw interrupt status bit for the USB_DEVICE_SERIAL_IN_EMPTY_INT interrupt."]
    #[inline(always)]
    pub fn serial_in_empty(&self) -> SERIAL_IN_EMPTY_R {
        SERIAL_IN_EMPTY_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The raw interrupt status bit for the USB_DEVICE_PID_ERR_INT interrupt."]
    #[inline(always)]
    pub fn pid_err(&self) -> PID_ERR_R {
        PID_ERR_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The raw interrupt status bit for the USB_DEVICE_CRC5_ERR_INT interrupt."]
    #[inline(always)]
    pub fn crc5_err(&self) -> CRC5_ERR_R {
        CRC5_ERR_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The raw interrupt status bit for the USB_DEVICE_CRC16_ERR_INT interrupt."]
    #[inline(always)]
    pub fn crc16_err(&self) -> CRC16_ERR_R {
        CRC16_ERR_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The raw interrupt status bit for the USB_DEVICE_STUFF_ERR_INT interrupt."]
    #[inline(always)]
    pub fn stuff_err(&self) -> STUFF_ERR_R {
        STUFF_ERR_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The raw interrupt status bit for the USB_DEVICE_IN_TOKEN_REC_IN_EP1_INT interrupt."]
    #[inline(always)]
    pub fn in_token_rec_in_ep1(&self) -> IN_TOKEN_REC_IN_EP1_R {
        IN_TOKEN_REC_IN_EP1_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The raw interrupt status bit for the USB_DEVICE_USB_BUS_RESET_INT interrupt."]
    #[inline(always)]
    pub fn usb_bus_reset(&self) -> USB_BUS_RESET_R {
        USB_BUS_RESET_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - The raw interrupt status bit for the USB_DEVICE_OUT_EP1_ZERO_PAYLOAD_INT interrupt."]
    #[inline(always)]
    pub fn out_ep1_zero_payload(&self) -> OUT_EP1_ZERO_PAYLOAD_R {
        OUT_EP1_ZERO_PAYLOAD_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - The raw interrupt status bit for the USB_DEVICE_OUT_EP2_ZERO_PAYLOAD_INT interrupt."]
    #[inline(always)]
    pub fn out_ep2_zero_payload(&self) -> OUT_EP2_ZERO_PAYLOAD_R {
        OUT_EP2_ZERO_PAYLOAD_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - The raw interrupt status bit for the USB_DEVICE_RTS_CHG_INT interrupt."]
    #[inline(always)]
    pub fn rts_chg(&self) -> RTS_CHG_R {
        RTS_CHG_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - The raw interrupt status bit for the USB_DEVICE_DTR_CHG_INT interrupt."]
    #[inline(always)]
    pub fn dtr_chg(&self) -> DTR_CHG_R {
        DTR_CHG_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - The raw interrupt status bit for the USB_DEVICE_GET_LINE_CODE_INT interrupt."]
    #[inline(always)]
    pub fn get_line_code(&self) -> GET_LINE_CODE_R {
        GET_LINE_CODE_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - The raw interrupt status bit for the USB_DEVICE_SET_LINE_CODE_INT interrupt."]
    #[inline(always)]
    pub fn set_line_code(&self) -> SET_LINE_CODE_R {
        SET_LINE_CODE_R::new(((self.bits >> 15) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_ST")
            .field("jtag_in_flush", &self.jtag_in_flush())
            .field("sof", &self.sof())
            .field("serial_out_recv_pkt", &self.serial_out_recv_pkt())
            .field("serial_in_empty", &self.serial_in_empty())
            .field("pid_err", &self.pid_err())
            .field("crc5_err", &self.crc5_err())
            .field("crc16_err", &self.crc16_err())
            .field("stuff_err", &self.stuff_err())
            .field("in_token_rec_in_ep1", &self.in_token_rec_in_ep1())
            .field("usb_bus_reset", &self.usb_bus_reset())
            .field("out_ep1_zero_payload", &self.out_ep1_zero_payload())
            .field("out_ep2_zero_payload", &self.out_ep2_zero_payload())
            .field("rts_chg", &self.rts_chg())
            .field("dtr_chg", &self.dtr_chg())
            .field("get_line_code", &self.get_line_code())
            .field("set_line_code", &self.set_line_code())
            .finish()
    }
}
#[doc = "Interrupt status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_ST_SPEC;
impl crate::RegisterSpec for INT_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_st::R`](R) reader structure"]
impl crate::Readable for INT_ST_SPEC {}
#[doc = "`reset()` method sets INT_ST to value 0"]
impl crate::Resettable for INT_ST_SPEC {}
