#[doc = "Register `OUT_EP1_ST` reader"]
pub type R = crate::R<OUT_EP1_ST_SPEC>;
#[doc = "Field `OUT_EP1_STATE` reader - State of OUT Endpoint 1."]
pub type OUT_EP1_STATE_R = crate::FieldReader;
#[doc = "Field `OUT_EP1_WR_ADDR` reader - Write data address of OUT endpoint 1. When USB_DEVICE_SERIAL_OUT_RECV_PKT_INT is detected, there are USB_DEVICE_OUT_EP1_WR_ADDR-2 bytes data in OUT EP1."]
pub type OUT_EP1_WR_ADDR_R = crate::FieldReader;
#[doc = "Field `OUT_EP1_RD_ADDR` reader - Read data address of OUT endpoint 1."]
pub type OUT_EP1_RD_ADDR_R = crate::FieldReader;
#[doc = "Field `OUT_EP1_REC_DATA_CNT` reader - Data count in OUT endpoint 1 when one packet is received."]
pub type OUT_EP1_REC_DATA_CNT_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:1 - State of OUT Endpoint 1."]
    #[inline(always)]
    pub fn out_ep1_state(&self) -> OUT_EP1_STATE_R {
        OUT_EP1_STATE_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:8 - Write data address of OUT endpoint 1. When USB_DEVICE_SERIAL_OUT_RECV_PKT_INT is detected, there are USB_DEVICE_OUT_EP1_WR_ADDR-2 bytes data in OUT EP1."]
    #[inline(always)]
    pub fn out_ep1_wr_addr(&self) -> OUT_EP1_WR_ADDR_R {
        OUT_EP1_WR_ADDR_R::new(((self.bits >> 2) & 0x7f) as u8)
    }
    #[doc = "Bits 9:15 - Read data address of OUT endpoint 1."]
    #[inline(always)]
    pub fn out_ep1_rd_addr(&self) -> OUT_EP1_RD_ADDR_R {
        OUT_EP1_RD_ADDR_R::new(((self.bits >> 9) & 0x7f) as u8)
    }
    #[doc = "Bits 16:22 - Data count in OUT endpoint 1 when one packet is received."]
    #[inline(always)]
    pub fn out_ep1_rec_data_cnt(&self) -> OUT_EP1_REC_DATA_CNT_R {
        OUT_EP1_REC_DATA_CNT_R::new(((self.bits >> 16) & 0x7f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("OUT_EP1_ST")
            .field("out_ep1_state", &self.out_ep1_state())
            .field("out_ep1_wr_addr", &self.out_ep1_wr_addr())
            .field("out_ep1_rd_addr", &self.out_ep1_rd_addr())
            .field("out_ep1_rec_data_cnt", &self.out_ep1_rec_data_cnt())
            .finish()
    }
}
#[doc = "CDC-ACM OUT endpoint status information.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_ep1_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OUT_EP1_ST_SPEC;
impl crate::RegisterSpec for OUT_EP1_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`out_ep1_st::R`](R) reader structure"]
impl crate::Readable for OUT_EP1_ST_SPEC {}
#[doc = "`reset()` method sets OUT_EP1_ST to value 0"]
impl crate::Resettable for OUT_EP1_ST_SPEC {}
