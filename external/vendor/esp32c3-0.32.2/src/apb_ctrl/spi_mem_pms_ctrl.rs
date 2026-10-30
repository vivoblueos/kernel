#[doc = "Register `SPI_MEM_PMS_CTRL` reader"]
pub type R = crate::R<SPI_MEM_PMS_CTRL_SPEC>;
#[doc = "Register `SPI_MEM_PMS_CTRL` writer"]
pub type W = crate::W<SPI_MEM_PMS_CTRL_SPEC>;
#[doc = "Field `SPI_MEM_REJECT_INT` reader - reg_spi_mem_reject_int"]
pub type SPI_MEM_REJECT_INT_R = crate::BitReader;
#[doc = "Field `SPI_MEM_REJECT_CLR` writer - reg_spi_mem_reject_clr"]
pub type SPI_MEM_REJECT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI_MEM_REJECT_CDE` reader - reg_spi_mem_reject_cde"]
pub type SPI_MEM_REJECT_CDE_R = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - reg_spi_mem_reject_int"]
    #[inline(always)]
    pub fn spi_mem_reject_int(&self) -> SPI_MEM_REJECT_INT_R {
        SPI_MEM_REJECT_INT_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 2:6 - reg_spi_mem_reject_cde"]
    #[inline(always)]
    pub fn spi_mem_reject_cde(&self) -> SPI_MEM_REJECT_CDE_R {
        SPI_MEM_REJECT_CDE_R::new(((self.bits >> 2) & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SPI_MEM_PMS_CTRL")
            .field("spi_mem_reject_int", &self.spi_mem_reject_int())
            .field("spi_mem_reject_cde", &self.spi_mem_reject_cde())
            .finish()
    }
}
impl W {
    #[doc = "Bit 1 - reg_spi_mem_reject_clr"]
    #[inline(always)]
    pub fn spi_mem_reject_clr(&mut self) -> SPI_MEM_REJECT_CLR_W<'_, SPI_MEM_PMS_CTRL_SPEC> {
        SPI_MEM_REJECT_CLR_W::new(self, 1)
    }
}
#[doc = "APB_CTRL_SPI_MEM_PMS_CTRL_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`spi_mem_pms_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`spi_mem_pms_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SPI_MEM_PMS_CTRL_SPEC;
impl crate::RegisterSpec for SPI_MEM_PMS_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`spi_mem_pms_ctrl::R`](R) reader structure"]
impl crate::Readable for SPI_MEM_PMS_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`spi_mem_pms_ctrl::W`](W) writer structure"]
impl crate::Writable for SPI_MEM_PMS_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SPI_MEM_PMS_CTRL to value 0"]
impl crate::Resettable for SPI_MEM_PMS_CTRL_SPEC {}
