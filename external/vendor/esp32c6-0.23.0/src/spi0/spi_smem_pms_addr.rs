#[doc = "Register `SPI_SMEM_PMS%s_ADDR` reader"]
pub type R = crate::R<SPI_SMEM_PMS_ADDR_SPEC>;
#[doc = "Register `SPI_SMEM_PMS%s_ADDR` writer"]
pub type W = crate::W<SPI_SMEM_PMS_ADDR_SPEC>;
#[doc = "Field `S` reader - SPI1 external RAM ACE section %s start address value"]
pub type S_R = crate::FieldReader<u32>;
#[doc = "Field `S` writer - SPI1 external RAM ACE section %s start address value"]
pub type S_W<'a, REG> = crate::FieldWriter<'a, REG, 26, u32>;
impl R {
    #[doc = "Bits 0:25 - SPI1 external RAM ACE section %s start address value"]
    #[inline(always)]
    pub fn s(&self) -> S_R {
        S_R::new(self.bits & 0x03ff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SPI_SMEM_PMS_ADDR")
            .field("s", &self.s())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:25 - SPI1 external RAM ACE section %s start address value"]
    #[inline(always)]
    pub fn s(&mut self) -> S_W<'_, SPI_SMEM_PMS_ADDR_SPEC> {
        S_W::new(self, 0)
    }
}
#[doc = "SPI1 external RAM ACE section %s start address register\n\nYou can [`read`](crate::Reg::read) this register and get [`spi_smem_pms_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`spi_smem_pms_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SPI_SMEM_PMS_ADDR_SPEC;
impl crate::RegisterSpec for SPI_SMEM_PMS_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`spi_smem_pms_addr::R`](R) reader structure"]
impl crate::Readable for SPI_SMEM_PMS_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`spi_smem_pms_addr::W`](W) writer structure"]
impl crate::Writable for SPI_SMEM_PMS_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SPI_SMEM_PMS%s_ADDR to value 0"]
impl crate::Resettable for SPI_SMEM_PMS_ADDR_SPEC {}
