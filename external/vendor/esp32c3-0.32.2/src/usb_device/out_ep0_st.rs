#[doc = "Register `OUT_EP0_ST` reader"]
pub type R = crate::R<OUT_EP0_ST_SPEC>;
#[doc = "Field `OUT_EP0_STATE` reader - State of OUT Endpoint 0."]
pub type OUT_EP0_STATE_R = crate::FieldReader;
#[doc = "Field `OUT_EP0_WR_ADDR` reader - Write data address of OUT endpoint 0. When USB_DEVICE_SERIAL_OUT_RECV_PKT_INT is detected, there are USB_DEVICE_OUT_EP0_WR_ADDR-2 bytes data in OUT EP0."]
pub type OUT_EP0_WR_ADDR_R = crate::FieldReader;
#[doc = "Field `OUT_EP0_RD_ADDR` reader - Read data address of OUT endpoint 0."]
pub type OUT_EP0_RD_ADDR_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:1 - State of OUT Endpoint 0."]
    #[inline(always)]
    pub fn out_ep0_state(&self) -> OUT_EP0_STATE_R {
        OUT_EP0_STATE_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:8 - Write data address of OUT endpoint 0. When USB_DEVICE_SERIAL_OUT_RECV_PKT_INT is detected, there are USB_DEVICE_OUT_EP0_WR_ADDR-2 bytes data in OUT EP0."]
    #[inline(always)]
    pub fn out_ep0_wr_addr(&self) -> OUT_EP0_WR_ADDR_R {
        OUT_EP0_WR_ADDR_R::new(((self.bits >> 2) & 0x7f) as u8)
    }
    #[doc = "Bits 9:15 - Read data address of OUT endpoint 0."]
    #[inline(always)]
    pub fn out_ep0_rd_addr(&self) -> OUT_EP0_RD_ADDR_R {
        OUT_EP0_RD_ADDR_R::new(((self.bits >> 9) & 0x7f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("OUT_EP0_ST")
            .field("out_ep0_state", &self.out_ep0_state())
            .field("out_ep0_wr_addr", &self.out_ep0_wr_addr())
            .field("out_ep0_rd_addr", &self.out_ep0_rd_addr())
            .finish()
    }
}
#[doc = "USB_DEVICE_OUT_EP0_ST_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_ep0_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OUT_EP0_ST_SPEC;
impl crate::RegisterSpec for OUT_EP0_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`out_ep0_st::R`](R) reader structure"]
impl crate::Readable for OUT_EP0_ST_SPEC {}
#[doc = "`reset()` method sets OUT_EP0_ST to value 0"]
impl crate::Resettable for OUT_EP0_ST_SPEC {}
