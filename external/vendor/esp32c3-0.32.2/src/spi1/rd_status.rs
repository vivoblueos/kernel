#[doc = "Register `RD_STATUS` reader"]
pub type R = crate::R<RD_STATUS_SPEC>;
#[doc = "Register `RD_STATUS` writer"]
pub type W = crate::W<RD_STATUS_SPEC>;
#[doc = "Field `STATUS` reader - The value is stored when set spi_mem_flash_rdsr bit and spi_mem_flash_res bit."]
pub type STATUS_R = crate::FieldReader<u16>;
#[doc = "Field `STATUS` writer - The value is stored when set spi_mem_flash_rdsr bit and spi_mem_flash_res bit."]
pub type STATUS_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `WB_MODE` reader - Mode bits in the flash fast read mode it is combined with spi_mem_fastrd_mode bit."]
pub type WB_MODE_R = crate::FieldReader;
#[doc = "Field `WB_MODE` writer - Mode bits in the flash fast read mode it is combined with spi_mem_fastrd_mode bit."]
pub type WB_MODE_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:15 - The value is stored when set spi_mem_flash_rdsr bit and spi_mem_flash_res bit."]
    #[inline(always)]
    pub fn status(&self) -> STATUS_R {
        STATUS_R::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:23 - Mode bits in the flash fast read mode it is combined with spi_mem_fastrd_mode bit."]
    #[inline(always)]
    pub fn wb_mode(&self) -> WB_MODE_R {
        WB_MODE_R::new(((self.bits >> 16) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_STATUS")
            .field("status", &self.status())
            .field("wb_mode", &self.wb_mode())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - The value is stored when set spi_mem_flash_rdsr bit and spi_mem_flash_res bit."]
    #[inline(always)]
    pub fn status(&mut self) -> STATUS_W<'_, RD_STATUS_SPEC> {
        STATUS_W::new(self, 0)
    }
    #[doc = "Bits 16:23 - Mode bits in the flash fast read mode it is combined with spi_mem_fastrd_mode bit."]
    #[inline(always)]
    pub fn wb_mode(&mut self) -> WB_MODE_W<'_, RD_STATUS_SPEC> {
        WB_MODE_W::new(self, 16)
    }
}
#[doc = "SPI1 status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_status::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rd_status::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_STATUS_SPEC;
impl crate::RegisterSpec for RD_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_status::R`](R) reader structure"]
impl crate::Readable for RD_STATUS_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rd_status::W`](W) writer structure"]
impl crate::Writable for RD_STATUS_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RD_STATUS to value 0"]
impl crate::Resettable for RD_STATUS_SPEC {}
