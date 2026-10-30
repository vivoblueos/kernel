#[doc = "Register `TXDMA_ERR` reader"]
pub type R = crate::R<TXDMA_ERR_SPEC>;
#[doc = "Register `TXDMA_ERR` writer"]
pub type W = crate::W<TXDMA_ERR_SPEC>;
#[doc = "Field `TXDMA_ERR` reader - "]
pub type TXDMA_ERR_R = crate::FieldReader;
#[doc = "Field `TXDMA_ERR` writer - "]
pub type TXDMA_ERR_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn txdma_err(&self) -> TXDMA_ERR_R {
        TXDMA_ERR_R::new((self.bits & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TXDMA_ERR")
            .field("txdma_err", &self.txdma_err())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn txdma_err(&mut self) -> TXDMA_ERR_W<'_, TXDMA_ERR_SPEC> {
        TXDMA_ERR_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`txdma_err::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txdma_err::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TXDMA_ERR_SPEC;
impl crate::RegisterSpec for TXDMA_ERR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`txdma_err::R`](R) reader structure"]
impl crate::Readable for TXDMA_ERR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`txdma_err::W`](W) writer structure"]
impl crate::Writable for TXDMA_ERR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TXDMA_ERR to value 0"]
impl crate::Resettable for TXDMA_ERR_SPEC {}
