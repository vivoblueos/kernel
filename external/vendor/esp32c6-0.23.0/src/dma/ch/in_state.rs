#[doc = "Register `IN_STATE` reader"]
pub type R = crate::R<IN_STATE_SPEC>;
#[doc = "Field `INLINK_DSCR_ADDR` reader - This register stores the current inlink descriptor's address."]
pub type INLINK_DSCR_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `IN_DSCR_STATE` reader - reserved"]
pub type IN_DSCR_STATE_R = crate::FieldReader;
#[doc = "Field `IN_STATE` reader - reserved"]
pub type IN_STATE_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:17 - This register stores the current inlink descriptor's address."]
    #[inline(always)]
    pub fn inlink_dscr_addr(&self) -> INLINK_DSCR_ADDR_R {
        INLINK_DSCR_ADDR_R::new(self.bits & 0x0003_ffff)
    }
    #[doc = "Bits 18:19 - reserved"]
    #[inline(always)]
    pub fn in_dscr_state(&self) -> IN_DSCR_STATE_R {
        IN_DSCR_STATE_R::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bits 20:22 - reserved"]
    #[inline(always)]
    pub fn in_state(&self) -> IN_STATE_R {
        IN_STATE_R::new(((self.bits >> 20) & 7) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IN_STATE")
            .field("inlink_dscr_addr", &self.inlink_dscr_addr())
            .field("in_dscr_state", &self.in_dscr_state())
            .field("in_state", &self.in_state())
            .finish()
    }
}
#[doc = "Receive status of Rx channel 0\n\nYou can [`read`](crate::Reg::read) this register and get [`in_state::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IN_STATE_SPEC;
impl crate::RegisterSpec for IN_STATE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`in_state::R`](R) reader structure"]
impl crate::Readable for IN_STATE_SPEC {}
#[doc = "`reset()` method sets IN_STATE to value 0"]
impl crate::Resettable for IN_STATE_SPEC {}
