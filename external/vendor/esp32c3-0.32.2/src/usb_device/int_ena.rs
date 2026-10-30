#[doc = "Register `INT_ENA` reader"]
pub type R = crate::R<INT_ENA_SPEC>;
#[doc = "Register `INT_ENA` writer"]
pub type W = crate::W<INT_ENA_SPEC>;
#[doc = "Field `JTAG_IN_FLUSH` reader - The interrupt enable bit for the USB_DEVICE_JTAG_IN_FLUSH_INT interrupt."]
pub type JTAG_IN_FLUSH_R = crate::BitReader;
#[doc = "Field `JTAG_IN_FLUSH` writer - The interrupt enable bit for the USB_DEVICE_JTAG_IN_FLUSH_INT interrupt."]
pub type JTAG_IN_FLUSH_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SOF` reader - The interrupt enable bit for the USB_DEVICE_SOF_INT interrupt."]
pub type SOF_R = crate::BitReader;
#[doc = "Field `SOF` writer - The interrupt enable bit for the USB_DEVICE_SOF_INT interrupt."]
pub type SOF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SERIAL_OUT_RECV_PKT` reader - The interrupt enable bit for the USB_DEVICE_SERIAL_OUT_RECV_PKT_INT interrupt."]
pub type SERIAL_OUT_RECV_PKT_R = crate::BitReader;
#[doc = "Field `SERIAL_OUT_RECV_PKT` writer - The interrupt enable bit for the USB_DEVICE_SERIAL_OUT_RECV_PKT_INT interrupt."]
pub type SERIAL_OUT_RECV_PKT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SERIAL_IN_EMPTY` reader - The interrupt enable bit for the USB_DEVICE_SERIAL_IN_EMPTY_INT interrupt."]
pub type SERIAL_IN_EMPTY_R = crate::BitReader;
#[doc = "Field `SERIAL_IN_EMPTY` writer - The interrupt enable bit for the USB_DEVICE_SERIAL_IN_EMPTY_INT interrupt."]
pub type SERIAL_IN_EMPTY_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PID_ERR` reader - The interrupt enable bit for the USB_DEVICE_PID_ERR_INT interrupt."]
pub type PID_ERR_R = crate::BitReader;
#[doc = "Field `PID_ERR` writer - The interrupt enable bit for the USB_DEVICE_PID_ERR_INT interrupt."]
pub type PID_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CRC5_ERR` reader - The interrupt enable bit for the USB_DEVICE_CRC5_ERR_INT interrupt."]
pub type CRC5_ERR_R = crate::BitReader;
#[doc = "Field `CRC5_ERR` writer - The interrupt enable bit for the USB_DEVICE_CRC5_ERR_INT interrupt."]
pub type CRC5_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CRC16_ERR` reader - The interrupt enable bit for the USB_DEVICE_CRC16_ERR_INT interrupt."]
pub type CRC16_ERR_R = crate::BitReader;
#[doc = "Field `CRC16_ERR` writer - The interrupt enable bit for the USB_DEVICE_CRC16_ERR_INT interrupt."]
pub type CRC16_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STUFF_ERR` reader - The interrupt enable bit for the USB_DEVICE_STUFF_ERR_INT interrupt."]
pub type STUFF_ERR_R = crate::BitReader;
#[doc = "Field `STUFF_ERR` writer - The interrupt enable bit for the USB_DEVICE_STUFF_ERR_INT interrupt."]
pub type STUFF_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IN_TOKEN_REC_IN_EP1` reader - The interrupt enable bit for the USB_DEVICE_IN_TOKEN_REC_IN_EP1_INT interrupt."]
pub type IN_TOKEN_REC_IN_EP1_R = crate::BitReader;
#[doc = "Field `IN_TOKEN_REC_IN_EP1` writer - The interrupt enable bit for the USB_DEVICE_IN_TOKEN_REC_IN_EP1_INT interrupt."]
pub type IN_TOKEN_REC_IN_EP1_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USB_BUS_RESET` reader - The interrupt enable bit for the USB_DEVICE_USB_BUS_RESET_INT interrupt."]
pub type USB_BUS_RESET_R = crate::BitReader;
#[doc = "Field `USB_BUS_RESET` writer - The interrupt enable bit for the USB_DEVICE_USB_BUS_RESET_INT interrupt."]
pub type USB_BUS_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OUT_EP1_ZERO_PAYLOAD` reader - The interrupt enable bit for the USB_DEVICE_OUT_EP1_ZERO_PAYLOAD_INT interrupt."]
pub type OUT_EP1_ZERO_PAYLOAD_R = crate::BitReader;
#[doc = "Field `OUT_EP1_ZERO_PAYLOAD` writer - The interrupt enable bit for the USB_DEVICE_OUT_EP1_ZERO_PAYLOAD_INT interrupt."]
pub type OUT_EP1_ZERO_PAYLOAD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OUT_EP2_ZERO_PAYLOAD` reader - The interrupt enable bit for the USB_DEVICE_OUT_EP2_ZERO_PAYLOAD_INT interrupt."]
pub type OUT_EP2_ZERO_PAYLOAD_R = crate::BitReader;
#[doc = "Field `OUT_EP2_ZERO_PAYLOAD` writer - The interrupt enable bit for the USB_DEVICE_OUT_EP2_ZERO_PAYLOAD_INT interrupt."]
pub type OUT_EP2_ZERO_PAYLOAD_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The interrupt enable bit for the USB_DEVICE_JTAG_IN_FLUSH_INT interrupt."]
    #[inline(always)]
    pub fn jtag_in_flush(&self) -> JTAG_IN_FLUSH_R {
        JTAG_IN_FLUSH_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The interrupt enable bit for the USB_DEVICE_SOF_INT interrupt."]
    #[inline(always)]
    pub fn sof(&self) -> SOF_R {
        SOF_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The interrupt enable bit for the USB_DEVICE_SERIAL_OUT_RECV_PKT_INT interrupt."]
    #[inline(always)]
    pub fn serial_out_recv_pkt(&self) -> SERIAL_OUT_RECV_PKT_R {
        SERIAL_OUT_RECV_PKT_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The interrupt enable bit for the USB_DEVICE_SERIAL_IN_EMPTY_INT interrupt."]
    #[inline(always)]
    pub fn serial_in_empty(&self) -> SERIAL_IN_EMPTY_R {
        SERIAL_IN_EMPTY_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The interrupt enable bit for the USB_DEVICE_PID_ERR_INT interrupt."]
    #[inline(always)]
    pub fn pid_err(&self) -> PID_ERR_R {
        PID_ERR_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The interrupt enable bit for the USB_DEVICE_CRC5_ERR_INT interrupt."]
    #[inline(always)]
    pub fn crc5_err(&self) -> CRC5_ERR_R {
        CRC5_ERR_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The interrupt enable bit for the USB_DEVICE_CRC16_ERR_INT interrupt."]
    #[inline(always)]
    pub fn crc16_err(&self) -> CRC16_ERR_R {
        CRC16_ERR_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The interrupt enable bit for the USB_DEVICE_STUFF_ERR_INT interrupt."]
    #[inline(always)]
    pub fn stuff_err(&self) -> STUFF_ERR_R {
        STUFF_ERR_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The interrupt enable bit for the USB_DEVICE_IN_TOKEN_REC_IN_EP1_INT interrupt."]
    #[inline(always)]
    pub fn in_token_rec_in_ep1(&self) -> IN_TOKEN_REC_IN_EP1_R {
        IN_TOKEN_REC_IN_EP1_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The interrupt enable bit for the USB_DEVICE_USB_BUS_RESET_INT interrupt."]
    #[inline(always)]
    pub fn usb_bus_reset(&self) -> USB_BUS_RESET_R {
        USB_BUS_RESET_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - The interrupt enable bit for the USB_DEVICE_OUT_EP1_ZERO_PAYLOAD_INT interrupt."]
    #[inline(always)]
    pub fn out_ep1_zero_payload(&self) -> OUT_EP1_ZERO_PAYLOAD_R {
        OUT_EP1_ZERO_PAYLOAD_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - The interrupt enable bit for the USB_DEVICE_OUT_EP2_ZERO_PAYLOAD_INT interrupt."]
    #[inline(always)]
    pub fn out_ep2_zero_payload(&self) -> OUT_EP2_ZERO_PAYLOAD_R {
        OUT_EP2_ZERO_PAYLOAD_R::new(((self.bits >> 11) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_ENA")
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
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The interrupt enable bit for the USB_DEVICE_JTAG_IN_FLUSH_INT interrupt."]
    #[inline(always)]
    pub fn jtag_in_flush(&mut self) -> JTAG_IN_FLUSH_W<'_, INT_ENA_SPEC> {
        JTAG_IN_FLUSH_W::new(self, 0)
    }
    #[doc = "Bit 1 - The interrupt enable bit for the USB_DEVICE_SOF_INT interrupt."]
    #[inline(always)]
    pub fn sof(&mut self) -> SOF_W<'_, INT_ENA_SPEC> {
        SOF_W::new(self, 1)
    }
    #[doc = "Bit 2 - The interrupt enable bit for the USB_DEVICE_SERIAL_OUT_RECV_PKT_INT interrupt."]
    #[inline(always)]
    pub fn serial_out_recv_pkt(&mut self) -> SERIAL_OUT_RECV_PKT_W<'_, INT_ENA_SPEC> {
        SERIAL_OUT_RECV_PKT_W::new(self, 2)
    }
    #[doc = "Bit 3 - The interrupt enable bit for the USB_DEVICE_SERIAL_IN_EMPTY_INT interrupt."]
    #[inline(always)]
    pub fn serial_in_empty(&mut self) -> SERIAL_IN_EMPTY_W<'_, INT_ENA_SPEC> {
        SERIAL_IN_EMPTY_W::new(self, 3)
    }
    #[doc = "Bit 4 - The interrupt enable bit for the USB_DEVICE_PID_ERR_INT interrupt."]
    #[inline(always)]
    pub fn pid_err(&mut self) -> PID_ERR_W<'_, INT_ENA_SPEC> {
        PID_ERR_W::new(self, 4)
    }
    #[doc = "Bit 5 - The interrupt enable bit for the USB_DEVICE_CRC5_ERR_INT interrupt."]
    #[inline(always)]
    pub fn crc5_err(&mut self) -> CRC5_ERR_W<'_, INT_ENA_SPEC> {
        CRC5_ERR_W::new(self, 5)
    }
    #[doc = "Bit 6 - The interrupt enable bit for the USB_DEVICE_CRC16_ERR_INT interrupt."]
    #[inline(always)]
    pub fn crc16_err(&mut self) -> CRC16_ERR_W<'_, INT_ENA_SPEC> {
        CRC16_ERR_W::new(self, 6)
    }
    #[doc = "Bit 7 - The interrupt enable bit for the USB_DEVICE_STUFF_ERR_INT interrupt."]
    #[inline(always)]
    pub fn stuff_err(&mut self) -> STUFF_ERR_W<'_, INT_ENA_SPEC> {
        STUFF_ERR_W::new(self, 7)
    }
    #[doc = "Bit 8 - The interrupt enable bit for the USB_DEVICE_IN_TOKEN_REC_IN_EP1_INT interrupt."]
    #[inline(always)]
    pub fn in_token_rec_in_ep1(&mut self) -> IN_TOKEN_REC_IN_EP1_W<'_, INT_ENA_SPEC> {
        IN_TOKEN_REC_IN_EP1_W::new(self, 8)
    }
    #[doc = "Bit 9 - The interrupt enable bit for the USB_DEVICE_USB_BUS_RESET_INT interrupt."]
    #[inline(always)]
    pub fn usb_bus_reset(&mut self) -> USB_BUS_RESET_W<'_, INT_ENA_SPEC> {
        USB_BUS_RESET_W::new(self, 9)
    }
    #[doc = "Bit 10 - The interrupt enable bit for the USB_DEVICE_OUT_EP1_ZERO_PAYLOAD_INT interrupt."]
    #[inline(always)]
    pub fn out_ep1_zero_payload(&mut self) -> OUT_EP1_ZERO_PAYLOAD_W<'_, INT_ENA_SPEC> {
        OUT_EP1_ZERO_PAYLOAD_W::new(self, 10)
    }
    #[doc = "Bit 11 - The interrupt enable bit for the USB_DEVICE_OUT_EP2_ZERO_PAYLOAD_INT interrupt."]
    #[inline(always)]
    pub fn out_ep2_zero_payload(&mut self) -> OUT_EP2_ZERO_PAYLOAD_W<'_, INT_ENA_SPEC> {
        OUT_EP2_ZERO_PAYLOAD_W::new(self, 11)
    }
}
#[doc = "USB_DEVICE_INT_ENA_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_ENA_SPEC;
impl crate::RegisterSpec for INT_ENA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_ena::R`](R) reader structure"]
impl crate::Readable for INT_ENA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`int_ena::W`](W) writer structure"]
impl crate::Writable for INT_ENA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_ENA to value 0"]
impl crate::Resettable for INT_ENA_SPEC {}
