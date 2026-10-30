#[doc = "Register `RESP3` reader"]
pub type R = crate::R<Resp3Spec>;
#[doc = "Field `RESP3` reader - Response register 3"]
pub type Resp3R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Response register 3"]
    #[inline(always)]
    pub fn resp3(&self) -> Resp3R {
        Resp3R::new(self.bits)
    }
}
#[doc = "Response register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`resp3::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Resp3Spec;
impl crate::RegisterSpec for Resp3Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`resp3::R`](R) reader structure"]
impl crate::Readable for Resp3Spec {}
#[doc = "`reset()` method sets RESP3 to value 0"]
impl crate::Resettable for Resp3Spec {
    const RESET_VALUE: u32 = 0;
}
