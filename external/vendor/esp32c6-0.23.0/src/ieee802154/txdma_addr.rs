#[doc = "Register `TXDMA_ADDR` reader"]
pub type R = crate::R<TXDMA_ADDR_SPEC>;
#[doc = "Register `TXDMA_ADDR` writer"]
pub type W = crate::W<TXDMA_ADDR_SPEC>;
#[doc = "Field `TXDMA_ADDR` reader - "]
pub type TXDMA_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `TXDMA_ADDR` writer - "]
pub type TXDMA_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn txdma_addr(&self) -> TXDMA_ADDR_R {
        TXDMA_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TXDMA_ADDR")
            .field("txdma_addr", &self.txdma_addr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn txdma_addr(&mut self) -> TXDMA_ADDR_W<'_, TXDMA_ADDR_SPEC> {
        TXDMA_ADDR_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`txdma_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txdma_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TXDMA_ADDR_SPEC;
impl crate::RegisterSpec for TXDMA_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`txdma_addr::R`](R) reader structure"]
impl crate::Readable for TXDMA_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`txdma_addr::W`](W) writer structure"]
impl crate::Writable for TXDMA_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TXDMA_ADDR to value 0"]
impl crate::Resettable for TXDMA_ADDR_SPEC {}
