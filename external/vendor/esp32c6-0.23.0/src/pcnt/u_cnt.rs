#[doc = "Register `U%s_CNT` reader"]
pub type R = crate::R<U_CNT_SPEC>;
#[doc = "Field `CNT` reader - This register stores the current pulse count value for unit %s."]
pub type CNT_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - This register stores the current pulse count value for unit %s."]
    #[inline(always)]
    pub fn cnt(&self) -> CNT_R {
        CNT_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("U_CNT").field("cnt", &self.cnt()).finish()
    }
}
#[doc = "Counter value for unit %s\n\nYou can [`read`](crate::Reg::read) this register and get [`u_cnt::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct U_CNT_SPEC;
impl crate::RegisterSpec for U_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`u_cnt::R`](R) reader structure"]
impl crate::Readable for U_CNT_SPEC {}
#[doc = "`reset()` method sets U%s_CNT to value 0"]
impl crate::Resettable for U_CNT_SPEC {}
