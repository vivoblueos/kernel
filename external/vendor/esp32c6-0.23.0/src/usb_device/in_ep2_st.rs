#[doc = "Register `IN_EP2_ST` reader"]
pub type R = crate::R<IN_EP2_ST_SPEC>;
#[doc = "Field `IN_EP2_STATE` reader - State of IN Endpoint 2."]
pub type IN_EP2_STATE_R = crate::FieldReader;
#[doc = "Field `IN_EP2_WR_ADDR` reader - Write data address of IN endpoint 2."]
pub type IN_EP2_WR_ADDR_R = crate::FieldReader;
#[doc = "Field `IN_EP2_RD_ADDR` reader - Read data address of IN endpoint 2."]
pub type IN_EP2_RD_ADDR_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:1 - State of IN Endpoint 2."]
    #[inline(always)]
    pub fn in_ep2_state(&self) -> IN_EP2_STATE_R {
        IN_EP2_STATE_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:8 - Write data address of IN endpoint 2."]
    #[inline(always)]
    pub fn in_ep2_wr_addr(&self) -> IN_EP2_WR_ADDR_R {
        IN_EP2_WR_ADDR_R::new(((self.bits >> 2) & 0x7f) as u8)
    }
    #[doc = "Bits 9:15 - Read data address of IN endpoint 2."]
    #[inline(always)]
    pub fn in_ep2_rd_addr(&self) -> IN_EP2_RD_ADDR_R {
        IN_EP2_RD_ADDR_R::new(((self.bits >> 9) & 0x7f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IN_EP2_ST")
            .field("in_ep2_state", &self.in_ep2_state())
            .field("in_ep2_wr_addr", &self.in_ep2_wr_addr())
            .field("in_ep2_rd_addr", &self.in_ep2_rd_addr())
            .finish()
    }
}
#[doc = "CDC-ACM interrupt IN endpoint status information.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_ep2_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IN_EP2_ST_SPEC;
impl crate::RegisterSpec for IN_EP2_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`in_ep2_st::R`](R) reader structure"]
impl crate::Readable for IN_EP2_ST_SPEC {}
#[doc = "`reset()` method sets IN_EP2_ST to value 0x01"]
impl crate::Resettable for IN_EP2_ST_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
