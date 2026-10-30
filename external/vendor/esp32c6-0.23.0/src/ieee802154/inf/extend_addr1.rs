#[doc = "Register `EXTEND_ADDR1` reader"]
pub type R = crate::R<EXTEND_ADDR1_SPEC>;
#[doc = "Register `EXTEND_ADDR1` writer"]
pub type W = crate::W<EXTEND_ADDR1_SPEC>;
#[doc = "Field `EXTEND_ADDR1` reader - "]
pub type EXTEND_ADDR1_R = crate::FieldReader<u32>;
#[doc = "Field `EXTEND_ADDR1` writer - "]
pub type EXTEND_ADDR1_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn extend_addr1(&self) -> EXTEND_ADDR1_R {
        EXTEND_ADDR1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("EXTEND_ADDR1")
            .field("extend_addr1", &self.extend_addr1())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn extend_addr1(&mut self) -> EXTEND_ADDR1_W<'_, EXTEND_ADDR1_SPEC> {
        EXTEND_ADDR1_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`extend_addr1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`extend_addr1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct EXTEND_ADDR1_SPEC;
impl crate::RegisterSpec for EXTEND_ADDR1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`extend_addr1::R`](R) reader structure"]
impl crate::Readable for EXTEND_ADDR1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`extend_addr1::W`](W) writer structure"]
impl crate::Writable for EXTEND_ADDR1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets EXTEND_ADDR1 to value 0"]
impl crate::Resettable for EXTEND_ADDR1_SPEC {}
