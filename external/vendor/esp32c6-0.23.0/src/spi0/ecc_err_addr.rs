#[doc = "Register `ECC_ERR_ADDR` reader"]
pub type R = crate::R<ECC_ERR_ADDR_SPEC>;
#[doc = "Field `ECC_ERR_ADDR` reader - This bits show the first MSPI ECC error address. It is cleared by when SPI_MEM_ECC_ERR_INT_CLR bit is set."]
pub type ECC_ERR_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `ECC_ERR_CNT` reader - This bits show the error times of MSPI ECC read. It is cleared by when SPI_MEM_ECC_ERR_INT_CLR bit is set."]
pub type ECC_ERR_CNT_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:25 - This bits show the first MSPI ECC error address. It is cleared by when SPI_MEM_ECC_ERR_INT_CLR bit is set."]
    #[inline(always)]
    pub fn ecc_err_addr(&self) -> ECC_ERR_ADDR_R {
        ECC_ERR_ADDR_R::new(self.bits & 0x03ff_ffff)
    }
    #[doc = "Bits 26:31 - This bits show the error times of MSPI ECC read. It is cleared by when SPI_MEM_ECC_ERR_INT_CLR bit is set."]
    #[inline(always)]
    pub fn ecc_err_cnt(&self) -> ECC_ERR_CNT_R {
        ECC_ERR_CNT_R::new(((self.bits >> 26) & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ECC_ERR_ADDR")
            .field("ecc_err_addr", &self.ecc_err_addr())
            .field("ecc_err_cnt", &self.ecc_err_cnt())
            .finish()
    }
}
#[doc = "MSPI ECC error address register\n\nYou can [`read`](crate::Reg::read) this register and get [`ecc_err_addr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ECC_ERR_ADDR_SPEC;
impl crate::RegisterSpec for ECC_ERR_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ecc_err_addr::R`](R) reader structure"]
impl crate::Readable for ECC_ERR_ADDR_SPEC {}
#[doc = "`reset()` method sets ECC_ERR_ADDR to value 0"]
impl crate::Resettable for ECC_ERR_ADDR_SPEC {}
