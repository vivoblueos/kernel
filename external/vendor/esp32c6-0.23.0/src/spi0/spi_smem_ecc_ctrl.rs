#[doc = "Register `SPI_SMEM_ECC_CTRL` reader"]
pub type R = crate::R<SPI_SMEM_ECC_CTRL_SPEC>;
#[doc = "Field `SPI_SMEM_ECC_ERR_INT_EN` reader - Set this bit to calculate the error times of MSPI ECC read when accesses to external RAM."]
pub type SPI_SMEM_ECC_ERR_INT_EN_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_PAGE_SIZE` reader - Set the page size of the external RAM accessed by MSPI. 0: 256 bytes. 1: 512 bytes. 2: 1024 bytes. 3: 2048 bytes."]
pub type SPI_SMEM_PAGE_SIZE_R = crate::FieldReader;
#[doc = "Field `SPI_SMEM_ECC_ADDR_EN` reader - Set this bit to enable MSPI ECC address conversion, no matter MSPI accesses to the ECC region or non-ECC region of external RAM. If there is no ECC region in external RAM, this bit should be 0. Otherwise, this bit should be 1."]
pub type SPI_SMEM_ECC_ADDR_EN_R = crate::BitReader;
impl R {
    #[doc = "Bit 17 - Set this bit to calculate the error times of MSPI ECC read when accesses to external RAM."]
    #[inline(always)]
    pub fn spi_smem_ecc_err_int_en(&self) -> SPI_SMEM_ECC_ERR_INT_EN_R {
        SPI_SMEM_ECC_ERR_INT_EN_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bits 18:19 - Set the page size of the external RAM accessed by MSPI. 0: 256 bytes. 1: 512 bytes. 2: 1024 bytes. 3: 2048 bytes."]
    #[inline(always)]
    pub fn spi_smem_page_size(&self) -> SPI_SMEM_PAGE_SIZE_R {
        SPI_SMEM_PAGE_SIZE_R::new(((self.bits >> 18) & 3) as u8)
    }
    #[doc = "Bit 20 - Set this bit to enable MSPI ECC address conversion, no matter MSPI accesses to the ECC region or non-ECC region of external RAM. If there is no ECC region in external RAM, this bit should be 0. Otherwise, this bit should be 1."]
    #[inline(always)]
    pub fn spi_smem_ecc_addr_en(&self) -> SPI_SMEM_ECC_ADDR_EN_R {
        SPI_SMEM_ECC_ADDR_EN_R::new(((self.bits >> 20) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SPI_SMEM_ECC_CTRL")
            .field("spi_smem_ecc_err_int_en", &self.spi_smem_ecc_err_int_en())
            .field("spi_smem_page_size", &self.spi_smem_page_size())
            .field("spi_smem_ecc_addr_en", &self.spi_smem_ecc_addr_en())
            .finish()
    }
}
#[doc = "MSPI ECC control register\n\nYou can [`read`](crate::Reg::read) this register and get [`spi_smem_ecc_ctrl::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SPI_SMEM_ECC_CTRL_SPEC;
impl crate::RegisterSpec for SPI_SMEM_ECC_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`spi_smem_ecc_ctrl::R`](R) reader structure"]
impl crate::Readable for SPI_SMEM_ECC_CTRL_SPEC {}
#[doc = "`reset()` method sets SPI_SMEM_ECC_CTRL to value 0x0008_0000"]
impl crate::Resettable for SPI_SMEM_ECC_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x0008_0000;
}
