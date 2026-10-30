#[doc = "Register `SPI_MEM_REJECT_ADDR` reader"]
pub type R = crate::R<SPI_MEM_REJECT_ADDR_SPEC>;
#[doc = "Field `SPI_MEM_REJECT_ADDR` reader - reg_spi_mem_reject_addr"]
pub type SPI_MEM_REJECT_ADDR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - reg_spi_mem_reject_addr"]
    #[inline(always)]
    pub fn spi_mem_reject_addr(&self) -> SPI_MEM_REJECT_ADDR_R {
        SPI_MEM_REJECT_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SPI_MEM_REJECT_ADDR")
            .field("spi_mem_reject_addr", &self.spi_mem_reject_addr())
            .finish()
    }
}
#[doc = "APB_CTRL_SPI_MEM_REJECT_ADDR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`spi_mem_reject_addr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SPI_MEM_REJECT_ADDR_SPEC;
impl crate::RegisterSpec for SPI_MEM_REJECT_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`spi_mem_reject_addr::R`](R) reader structure"]
impl crate::Readable for SPI_MEM_REJECT_ADDR_SPEC {}
#[doc = "`reset()` method sets SPI_MEM_REJECT_ADDR to value 0"]
impl crate::Resettable for SPI_MEM_REJECT_ADDR_SPEC {}
