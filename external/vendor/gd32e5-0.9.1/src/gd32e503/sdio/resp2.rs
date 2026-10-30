#[doc = "Register `RESP2` reader"]
pub type R = crate::R<Resp2Spec>;
#[doc = "Field `RESP2` reader - Card state"]
pub type Resp2R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Card state"]
    #[inline(always)]
    pub fn resp2(&self) -> Resp2R {
        Resp2R::new(self.bits)
    }
}
#[doc = "Response register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`resp2::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Resp2Spec;
impl crate::RegisterSpec for Resp2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`resp2::R`](R) reader structure"]
impl crate::Readable for Resp2Spec {}
#[doc = "`reset()` method sets RESP2 to value 0"]
impl crate::Resettable for Resp2Spec {
    const RESET_VALUE: u32 = 0;
}
