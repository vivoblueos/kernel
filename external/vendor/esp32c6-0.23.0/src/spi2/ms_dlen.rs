#[doc = "Register `MS_DLEN` reader"]
pub type R = crate::R<MS_DLEN_SPEC>;
#[doc = "Register `MS_DLEN` writer"]
pub type W = crate::W<MS_DLEN_SPEC>;
#[doc = "Field `MS_DATA_BITLEN` reader - The value of these bits is the configured SPI transmission data bit length in master mode DMA controlled transfer or CPU controlled transfer. The value is also the configured bit length in slave mode DMA RX controlled transfer. The register value shall be (bit_num-1). Can be configured in CONF state."]
pub type MS_DATA_BITLEN_R = crate::FieldReader<u32>;
#[doc = "Field `MS_DATA_BITLEN` writer - The value of these bits is the configured SPI transmission data bit length in master mode DMA controlled transfer or CPU controlled transfer. The value is also the configured bit length in slave mode DMA RX controlled transfer. The register value shall be (bit_num-1). Can be configured in CONF state."]
pub type MS_DATA_BITLEN_W<'a, REG> = crate::FieldWriter<'a, REG, 18, u32>;
impl R {
    #[doc = "Bits 0:17 - The value of these bits is the configured SPI transmission data bit length in master mode DMA controlled transfer or CPU controlled transfer. The value is also the configured bit length in slave mode DMA RX controlled transfer. The register value shall be (bit_num-1). Can be configured in CONF state."]
    #[inline(always)]
    pub fn ms_data_bitlen(&self) -> MS_DATA_BITLEN_R {
        MS_DATA_BITLEN_R::new(self.bits & 0x0003_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MS_DLEN")
            .field("ms_data_bitlen", &self.ms_data_bitlen())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:17 - The value of these bits is the configured SPI transmission data bit length in master mode DMA controlled transfer or CPU controlled transfer. The value is also the configured bit length in slave mode DMA RX controlled transfer. The register value shall be (bit_num-1). Can be configured in CONF state."]
    #[inline(always)]
    pub fn ms_data_bitlen(&mut self) -> MS_DATA_BITLEN_W<'_, MS_DLEN_SPEC> {
        MS_DATA_BITLEN_W::new(self, 0)
    }
}
#[doc = "SPI data bit length control register\n\nYou can [`read`](crate::Reg::read) this register and get [`ms_dlen::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ms_dlen::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MS_DLEN_SPEC;
impl crate::RegisterSpec for MS_DLEN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ms_dlen::R`](R) reader structure"]
impl crate::Readable for MS_DLEN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ms_dlen::W`](W) writer structure"]
impl crate::Writable for MS_DLEN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MS_DLEN to value 0"]
impl crate::Resettable for MS_DLEN_SPEC {}
