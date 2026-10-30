#[doc = "Register `SPI_SMEM_PMS%s_ATTR` reader"]
pub type R = crate::R<SPI_SMEM_PMS_ATTR_SPEC>;
#[doc = "Register `SPI_SMEM_PMS%s_ATTR` writer"]
pub type W = crate::W<SPI_SMEM_PMS_ATTR_SPEC>;
#[doc = "Field `SPI_SMEM_PMS_RD_ATTR` reader - 1: SPI1 external RAM ACE section %s read accessible. 0: Not allowed."]
pub type SPI_SMEM_PMS_RD_ATTR_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_PMS_RD_ATTR` writer - 1: SPI1 external RAM ACE section %s read accessible. 0: Not allowed."]
pub type SPI_SMEM_PMS_RD_ATTR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI_SMEM_PMS_WR_ATTR` reader - 1: SPI1 external RAM ACE section %s write accessible. 0: Not allowed."]
pub type SPI_SMEM_PMS_WR_ATTR_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_PMS_WR_ATTR` writer - 1: SPI1 external RAM ACE section %s write accessible. 0: Not allowed."]
pub type SPI_SMEM_PMS_WR_ATTR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI_SMEM_PMS_ECC` reader - SPI1 external RAM ACE section %s ECC mode, 1: enable ECC mode. 0: Disable it. The external RAM ACE section %s is configured by registers SPI_SMEM_PMS%s_ADDR_REG and SPI_SMEM_PMS%s_SIZE_REG."]
pub type SPI_SMEM_PMS_ECC_R = crate::BitReader;
#[doc = "Field `SPI_SMEM_PMS_ECC` writer - SPI1 external RAM ACE section %s ECC mode, 1: enable ECC mode. 0: Disable it. The external RAM ACE section %s is configured by registers SPI_SMEM_PMS%s_ADDR_REG and SPI_SMEM_PMS%s_SIZE_REG."]
pub type SPI_SMEM_PMS_ECC_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - 1: SPI1 external RAM ACE section %s read accessible. 0: Not allowed."]
    #[inline(always)]
    pub fn spi_smem_pms_rd_attr(&self) -> SPI_SMEM_PMS_RD_ATTR_R {
        SPI_SMEM_PMS_RD_ATTR_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - 1: SPI1 external RAM ACE section %s write accessible. 0: Not allowed."]
    #[inline(always)]
    pub fn spi_smem_pms_wr_attr(&self) -> SPI_SMEM_PMS_WR_ATTR_R {
        SPI_SMEM_PMS_WR_ATTR_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - SPI1 external RAM ACE section %s ECC mode, 1: enable ECC mode. 0: Disable it. The external RAM ACE section %s is configured by registers SPI_SMEM_PMS%s_ADDR_REG and SPI_SMEM_PMS%s_SIZE_REG."]
    #[inline(always)]
    pub fn spi_smem_pms_ecc(&self) -> SPI_SMEM_PMS_ECC_R {
        SPI_SMEM_PMS_ECC_R::new(((self.bits >> 2) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SPI_SMEM_PMS_ATTR")
            .field("spi_smem_pms_rd_attr", &self.spi_smem_pms_rd_attr())
            .field("spi_smem_pms_wr_attr", &self.spi_smem_pms_wr_attr())
            .field("spi_smem_pms_ecc", &self.spi_smem_pms_ecc())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - 1: SPI1 external RAM ACE section %s read accessible. 0: Not allowed."]
    #[inline(always)]
    pub fn spi_smem_pms_rd_attr(&mut self) -> SPI_SMEM_PMS_RD_ATTR_W<'_, SPI_SMEM_PMS_ATTR_SPEC> {
        SPI_SMEM_PMS_RD_ATTR_W::new(self, 0)
    }
    #[doc = "Bit 1 - 1: SPI1 external RAM ACE section %s write accessible. 0: Not allowed."]
    #[inline(always)]
    pub fn spi_smem_pms_wr_attr(&mut self) -> SPI_SMEM_PMS_WR_ATTR_W<'_, SPI_SMEM_PMS_ATTR_SPEC> {
        SPI_SMEM_PMS_WR_ATTR_W::new(self, 1)
    }
    #[doc = "Bit 2 - SPI1 external RAM ACE section %s ECC mode, 1: enable ECC mode. 0: Disable it. The external RAM ACE section %s is configured by registers SPI_SMEM_PMS%s_ADDR_REG and SPI_SMEM_PMS%s_SIZE_REG."]
    #[inline(always)]
    pub fn spi_smem_pms_ecc(&mut self) -> SPI_SMEM_PMS_ECC_W<'_, SPI_SMEM_PMS_ATTR_SPEC> {
        SPI_SMEM_PMS_ECC_W::new(self, 2)
    }
}
#[doc = "SPI1 flash ACE section %s start address register\n\nYou can [`read`](crate::Reg::read) this register and get [`spi_smem_pms_attr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`spi_smem_pms_attr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SPI_SMEM_PMS_ATTR_SPEC;
impl crate::RegisterSpec for SPI_SMEM_PMS_ATTR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`spi_smem_pms_attr::R`](R) reader structure"]
impl crate::Readable for SPI_SMEM_PMS_ATTR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`spi_smem_pms_attr::W`](W) writer structure"]
impl crate::Writable for SPI_SMEM_PMS_ATTR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SPI_SMEM_PMS%s_ATTR to value 0x03"]
impl crate::Resettable for SPI_SMEM_PMS_ATTR_SPEC {
    const RESET_VALUE: u32 = 0x03;
}
