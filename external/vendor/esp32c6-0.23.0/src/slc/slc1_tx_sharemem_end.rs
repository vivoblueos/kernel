#[doc = "Register `SLC1_TX_SHAREMEM_END` reader"]
pub type R = crate::R<SLC1_TX_SHAREMEM_END_SPEC>;
#[doc = "Register `SLC1_TX_SHAREMEM_END` writer"]
pub type W = crate::W<SLC1_TX_SHAREMEM_END_SPEC>;
#[doc = "Field `SDIO_SDIO_SLC1_TX_SHAREMEM_END_ADDR` reader - Configures SLC1 host to slave channel AHB end address boundary."]
pub type SDIO_SDIO_SLC1_TX_SHAREMEM_END_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `SDIO_SDIO_SLC1_TX_SHAREMEM_END_ADDR` writer - Configures SLC1 host to slave channel AHB end address boundary."]
pub type SDIO_SDIO_SLC1_TX_SHAREMEM_END_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Configures SLC1 host to slave channel AHB end address boundary."]
    #[inline(always)]
    pub fn sdio_sdio_slc1_tx_sharemem_end_addr(&self) -> SDIO_SDIO_SLC1_TX_SHAREMEM_END_ADDR_R {
        SDIO_SDIO_SLC1_TX_SHAREMEM_END_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC1_TX_SHAREMEM_END")
            .field(
                "sdio_sdio_slc1_tx_sharemem_end_addr",
                &self.sdio_sdio_slc1_tx_sharemem_end_addr(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Configures SLC1 host to slave channel AHB end address boundary."]
    #[inline(always)]
    pub fn sdio_sdio_slc1_tx_sharemem_end_addr(
        &mut self,
    ) -> SDIO_SDIO_SLC1_TX_SHAREMEM_END_ADDR_W<'_, SLC1_TX_SHAREMEM_END_SPEC> {
        SDIO_SDIO_SLC1_TX_SHAREMEM_END_ADDR_W::new(self, 0)
    }
}
#[doc = "SLC1 AHB TX end address range\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1_tx_sharemem_end::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1_tx_sharemem_end::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC1_TX_SHAREMEM_END_SPEC;
impl crate::RegisterSpec for SLC1_TX_SHAREMEM_END_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc1_tx_sharemem_end::R`](R) reader structure"]
impl crate::Readable for SLC1_TX_SHAREMEM_END_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slc1_tx_sharemem_end::W`](W) writer structure"]
impl crate::Writable for SLC1_TX_SHAREMEM_END_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC1_TX_SHAREMEM_END to value 0xffff_ffff"]
impl crate::Resettable for SLC1_TX_SHAREMEM_END_SPEC {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
