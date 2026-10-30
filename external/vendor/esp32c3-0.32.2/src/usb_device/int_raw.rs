#[doc = "Register `INT_RAW` reader"]
pub type R = crate::R<INT_RAW_SPEC>;
#[doc = "Register `INT_RAW` writer"]
pub type W = crate::W<INT_RAW_SPEC>;
#[doc = "Field `JTAG_IN_FLUSH` reader - The raw interrupt bit turns to high level when flush cmd is received for IN endpoint 2 of JTAG."]
pub type JTAG_IN_FLUSH_R = crate::BitReader;
#[doc = "Field `JTAG_IN_FLUSH` writer - The raw interrupt bit turns to high level when flush cmd is received for IN endpoint 2 of JTAG."]
pub type JTAG_IN_FLUSH_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SOF` reader - The raw interrupt bit turns to high level when SOF frame is received."]
pub type SOF_R = crate::BitReader;
#[doc = "Field `SOF` writer - The raw interrupt bit turns to high level when SOF frame is received."]
pub type SOF_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SERIAL_OUT_RECV_PKT` reader - The raw interrupt bit turns to high level when Serial Port OUT Endpoint received one packet."]
pub type SERIAL_OUT_RECV_PKT_R = crate::BitReader;
#[doc = "Field `SERIAL_OUT_RECV_PKT` writer - The raw interrupt bit turns to high level when Serial Port OUT Endpoint received one packet."]
pub type SERIAL_OUT_RECV_PKT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SERIAL_IN_EMPTY` reader - The raw interrupt bit turns to high level when Serial Port IN Endpoint is empty."]
pub type SERIAL_IN_EMPTY_R = crate::BitReader;
#[doc = "Field `SERIAL_IN_EMPTY` writer - The raw interrupt bit turns to high level when Serial Port IN Endpoint is empty."]
pub type SERIAL_IN_EMPTY_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PID_ERR` reader - The raw interrupt bit turns to high level when pid error is detected."]
pub type PID_ERR_R = crate::BitReader;
#[doc = "Field `PID_ERR` writer - The raw interrupt bit turns to high level when pid error is detected."]
pub type PID_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CRC5_ERR` reader - The raw interrupt bit turns to high level when CRC5 error is detected."]
pub type CRC5_ERR_R = crate::BitReader;
#[doc = "Field `CRC5_ERR` writer - The raw interrupt bit turns to high level when CRC5 error is detected."]
pub type CRC5_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CRC16_ERR` reader - The raw interrupt bit turns to high level when CRC16 error is detected."]
pub type CRC16_ERR_R = crate::BitReader;
#[doc = "Field `CRC16_ERR` writer - The raw interrupt bit turns to high level when CRC16 error is detected."]
pub type CRC16_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STUFF_ERR` reader - The raw interrupt bit turns to high level when stuff error is detected."]
pub type STUFF_ERR_R = crate::BitReader;
#[doc = "Field `STUFF_ERR` writer - The raw interrupt bit turns to high level when stuff error is detected."]
pub type STUFF_ERR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IN_TOKEN_REC_IN_EP1` reader - The raw interrupt bit turns to high level when IN token for IN endpoint 1 is received."]
pub type IN_TOKEN_REC_IN_EP1_R = crate::BitReader;
#[doc = "Field `IN_TOKEN_REC_IN_EP1` writer - The raw interrupt bit turns to high level when IN token for IN endpoint 1 is received."]
pub type IN_TOKEN_REC_IN_EP1_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USB_BUS_RESET` reader - The raw interrupt bit turns to high level when usb bus reset is detected."]
pub type USB_BUS_RESET_R = crate::BitReader;
#[doc = "Field `USB_BUS_RESET` writer - The raw interrupt bit turns to high level when usb bus reset is detected."]
pub type USB_BUS_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OUT_EP1_ZERO_PAYLOAD` reader - The raw interrupt bit turns to high level when OUT endpoint 1 received packet with zero palyload."]
pub type OUT_EP1_ZERO_PAYLOAD_R = crate::BitReader;
#[doc = "Field `OUT_EP1_ZERO_PAYLOAD` writer - The raw interrupt bit turns to high level when OUT endpoint 1 received packet with zero palyload."]
pub type OUT_EP1_ZERO_PAYLOAD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OUT_EP2_ZERO_PAYLOAD` reader - The raw interrupt bit turns to high level when OUT endpoint 2 received packet with zero palyload."]
pub type OUT_EP2_ZERO_PAYLOAD_R = crate::BitReader;
#[doc = "Field `OUT_EP2_ZERO_PAYLOAD` writer - The raw interrupt bit turns to high level when OUT endpoint 2 received packet with zero palyload."]
pub type OUT_EP2_ZERO_PAYLOAD_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The raw interrupt bit turns to high level when flush cmd is received for IN endpoint 2 of JTAG."]
    #[inline(always)]
    pub fn jtag_in_flush(&self) -> JTAG_IN_FLUSH_R {
        JTAG_IN_FLUSH_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The raw interrupt bit turns to high level when SOF frame is received."]
    #[inline(always)]
    pub fn sof(&self) -> SOF_R {
        SOF_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The raw interrupt bit turns to high level when Serial Port OUT Endpoint received one packet."]
    #[inline(always)]
    pub fn serial_out_recv_pkt(&self) -> SERIAL_OUT_RECV_PKT_R {
        SERIAL_OUT_RECV_PKT_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The raw interrupt bit turns to high level when Serial Port IN Endpoint is empty."]
    #[inline(always)]
    pub fn serial_in_empty(&self) -> SERIAL_IN_EMPTY_R {
        SERIAL_IN_EMPTY_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The raw interrupt bit turns to high level when pid error is detected."]
    #[inline(always)]
    pub fn pid_err(&self) -> PID_ERR_R {
        PID_ERR_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The raw interrupt bit turns to high level when CRC5 error is detected."]
    #[inline(always)]
    pub fn crc5_err(&self) -> CRC5_ERR_R {
        CRC5_ERR_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The raw interrupt bit turns to high level when CRC16 error is detected."]
    #[inline(always)]
    pub fn crc16_err(&self) -> CRC16_ERR_R {
        CRC16_ERR_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The raw interrupt bit turns to high level when stuff error is detected."]
    #[inline(always)]
    pub fn stuff_err(&self) -> STUFF_ERR_R {
        STUFF_ERR_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The raw interrupt bit turns to high level when IN token for IN endpoint 1 is received."]
    #[inline(always)]
    pub fn in_token_rec_in_ep1(&self) -> IN_TOKEN_REC_IN_EP1_R {
        IN_TOKEN_REC_IN_EP1_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The raw interrupt bit turns to high level when usb bus reset is detected."]
    #[inline(always)]
    pub fn usb_bus_reset(&self) -> USB_BUS_RESET_R {
        USB_BUS_RESET_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - The raw interrupt bit turns to high level when OUT endpoint 1 received packet with zero palyload."]
    #[inline(always)]
    pub fn out_ep1_zero_payload(&self) -> OUT_EP1_ZERO_PAYLOAD_R {
        OUT_EP1_ZERO_PAYLOAD_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - The raw interrupt bit turns to high level when OUT endpoint 2 received packet with zero palyload."]
    #[inline(always)]
    pub fn out_ep2_zero_payload(&self) -> OUT_EP2_ZERO_PAYLOAD_R {
        OUT_EP2_ZERO_PAYLOAD_R::new(((self.bits >> 11) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_RAW")
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
    #[doc = "Bit 0 - The raw interrupt bit turns to high level when flush cmd is received for IN endpoint 2 of JTAG."]
    #[inline(always)]
    pub fn jtag_in_flush(&mut self) -> JTAG_IN_FLUSH_W<'_, INT_RAW_SPEC> {
        JTAG_IN_FLUSH_W::new(self, 0)
    }
    #[doc = "Bit 1 - The raw interrupt bit turns to high level when SOF frame is received."]
    #[inline(always)]
    pub fn sof(&mut self) -> SOF_W<'_, INT_RAW_SPEC> {
        SOF_W::new(self, 1)
    }
    #[doc = "Bit 2 - The raw interrupt bit turns to high level when Serial Port OUT Endpoint received one packet."]
    #[inline(always)]
    pub fn serial_out_recv_pkt(&mut self) -> SERIAL_OUT_RECV_PKT_W<'_, INT_RAW_SPEC> {
        SERIAL_OUT_RECV_PKT_W::new(self, 2)
    }
    #[doc = "Bit 3 - The raw interrupt bit turns to high level when Serial Port IN Endpoint is empty."]
    #[inline(always)]
    pub fn serial_in_empty(&mut self) -> SERIAL_IN_EMPTY_W<'_, INT_RAW_SPEC> {
        SERIAL_IN_EMPTY_W::new(self, 3)
    }
    #[doc = "Bit 4 - The raw interrupt bit turns to high level when pid error is detected."]
    #[inline(always)]
    pub fn pid_err(&mut self) -> PID_ERR_W<'_, INT_RAW_SPEC> {
        PID_ERR_W::new(self, 4)
    }
    #[doc = "Bit 5 - The raw interrupt bit turns to high level when CRC5 error is detected."]
    #[inline(always)]
    pub fn crc5_err(&mut self) -> CRC5_ERR_W<'_, INT_RAW_SPEC> {
        CRC5_ERR_W::new(self, 5)
    }
    #[doc = "Bit 6 - The raw interrupt bit turns to high level when CRC16 error is detected."]
    #[inline(always)]
    pub fn crc16_err(&mut self) -> CRC16_ERR_W<'_, INT_RAW_SPEC> {
        CRC16_ERR_W::new(self, 6)
    }
    #[doc = "Bit 7 - The raw interrupt bit turns to high level when stuff error is detected."]
    #[inline(always)]
    pub fn stuff_err(&mut self) -> STUFF_ERR_W<'_, INT_RAW_SPEC> {
        STUFF_ERR_W::new(self, 7)
    }
    #[doc = "Bit 8 - The raw interrupt bit turns to high level when IN token for IN endpoint 1 is received."]
    #[inline(always)]
    pub fn in_token_rec_in_ep1(&mut self) -> IN_TOKEN_REC_IN_EP1_W<'_, INT_RAW_SPEC> {
        IN_TOKEN_REC_IN_EP1_W::new(self, 8)
    }
    #[doc = "Bit 9 - The raw interrupt bit turns to high level when usb bus reset is detected."]
    #[inline(always)]
    pub fn usb_bus_reset(&mut self) -> USB_BUS_RESET_W<'_, INT_RAW_SPEC> {
        USB_BUS_RESET_W::new(self, 9)
    }
    #[doc = "Bit 10 - The raw interrupt bit turns to high level when OUT endpoint 1 received packet with zero palyload."]
    #[inline(always)]
    pub fn out_ep1_zero_payload(&mut self) -> OUT_EP1_ZERO_PAYLOAD_W<'_, INT_RAW_SPEC> {
        OUT_EP1_ZERO_PAYLOAD_W::new(self, 10)
    }
    #[doc = "Bit 11 - The raw interrupt bit turns to high level when OUT endpoint 2 received packet with zero palyload."]
    #[inline(always)]
    pub fn out_ep2_zero_payload(&mut self) -> OUT_EP2_ZERO_PAYLOAD_W<'_, INT_RAW_SPEC> {
        OUT_EP2_ZERO_PAYLOAD_W::new(self, 11)
    }
}
#[doc = "USB_DEVICE_INT_RAW_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_raw::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_RAW_SPEC;
impl crate::RegisterSpec for INT_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_raw::R`](R) reader structure"]
impl crate::Readable for INT_RAW_SPEC {}
#[doc = "`write(|w| ..)` method takes [`int_raw::W`](W) writer structure"]
impl crate::Writable for INT_RAW_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_RAW to value 0x08"]
impl crate::Resettable for INT_RAW_SPEC {
    const RESET_VALUE: u32 = 0x08;
}
