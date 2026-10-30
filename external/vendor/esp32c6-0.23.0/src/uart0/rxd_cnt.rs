#[doc = "Register `RXD_CNT` reader"]
pub type R = crate::R<RXD_CNT_SPEC>;
#[doc = "Field `RXD_EDGE_CNT` reader - This register stores the count of rxd edge change. It is used in baud rate-detect process."]
pub type RXD_EDGE_CNT_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:9 - This register stores the count of rxd edge change. It is used in baud rate-detect process."]
    #[inline(always)]
    pub fn rxd_edge_cnt(&self) -> RXD_EDGE_CNT_R {
        RXD_EDGE_CNT_R::new((self.bits & 0x03ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RXD_CNT")
            .field("rxd_edge_cnt", &self.rxd_edge_cnt())
            .finish()
    }
}
#[doc = "Autobaud edge change count register\n\nYou can [`read`](crate::Reg::read) this register and get [`rxd_cnt::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RXD_CNT_SPEC;
impl crate::RegisterSpec for RXD_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rxd_cnt::R`](R) reader structure"]
impl crate::Readable for RXD_CNT_SPEC {}
#[doc = "`reset()` method sets RXD_CNT to value 0"]
impl crate::Resettable for RXD_CNT_SPEC {}
