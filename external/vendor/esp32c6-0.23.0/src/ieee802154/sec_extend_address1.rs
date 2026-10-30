#[doc = "Register `SEC_EXTEND_ADDRESS1` reader"]
pub type R = crate::R<SEC_EXTEND_ADDRESS1_SPEC>;
#[doc = "Register `SEC_EXTEND_ADDRESS1` writer"]
pub type W = crate::W<SEC_EXTEND_ADDRESS1_SPEC>;
#[doc = "Field `SEC_EXTEND_ADDRESS1` reader - "]
pub type SEC_EXTEND_ADDRESS1_R = crate::FieldReader<u32>;
#[doc = "Field `SEC_EXTEND_ADDRESS1` writer - "]
pub type SEC_EXTEND_ADDRESS1_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn sec_extend_address1(&self) -> SEC_EXTEND_ADDRESS1_R {
        SEC_EXTEND_ADDRESS1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SEC_EXTEND_ADDRESS1")
            .field("sec_extend_address1", &self.sec_extend_address1())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn sec_extend_address1(&mut self) -> SEC_EXTEND_ADDRESS1_W<'_, SEC_EXTEND_ADDRESS1_SPEC> {
        SEC_EXTEND_ADDRESS1_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`sec_extend_address1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sec_extend_address1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SEC_EXTEND_ADDRESS1_SPEC;
impl crate::RegisterSpec for SEC_EXTEND_ADDRESS1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sec_extend_address1::R`](R) reader structure"]
impl crate::Readable for SEC_EXTEND_ADDRESS1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sec_extend_address1::W`](W) writer structure"]
impl crate::Writable for SEC_EXTEND_ADDRESS1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SEC_EXTEND_ADDRESS1 to value 0"]
impl crate::Resettable for SEC_EXTEND_ADDRESS1_SPEC {}
