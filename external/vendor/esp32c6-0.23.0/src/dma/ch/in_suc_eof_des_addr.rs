#[doc = "Register `IN_SUC_EOF_DES_ADDR` reader"]
pub type R = crate::R<IN_SUC_EOF_DES_ADDR_SPEC>;
#[doc = "Field `IN_SUC_EOF_DES_ADDR` reader - This register stores the address of the inlink descriptor when the EOF bit in this descriptor is 1."]
pub type IN_SUC_EOF_DES_ADDR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - This register stores the address of the inlink descriptor when the EOF bit in this descriptor is 1."]
    #[inline(always)]
    pub fn in_suc_eof_des_addr(&self) -> IN_SUC_EOF_DES_ADDR_R {
        IN_SUC_EOF_DES_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IN_SUC_EOF_DES_ADDR")
            .field("in_suc_eof_des_addr", &self.in_suc_eof_des_addr())
            .finish()
    }
}
#[doc = "Inlink descriptor address when EOF occurs of Rx channel 0\n\nYou can [`read`](crate::Reg::read) this register and get [`in_suc_eof_des_addr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IN_SUC_EOF_DES_ADDR_SPEC;
impl crate::RegisterSpec for IN_SUC_EOF_DES_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`in_suc_eof_des_addr::R`](R) reader structure"]
impl crate::Readable for IN_SUC_EOF_DES_ADDR_SPEC {}
#[doc = "`reset()` method sets IN_SUC_EOF_DES_ADDR to value 0"]
impl crate::Resettable for IN_SUC_EOF_DES_ADDR_SPEC {}
