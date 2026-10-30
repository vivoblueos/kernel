#[doc = "Register `XTS_PHYSICAL_ADDRESS` reader"]
pub type R = crate::R<XTS_PHYSICAL_ADDRESS_SPEC>;
#[doc = "Register `XTS_PHYSICAL_ADDRESS` writer"]
pub type W = crate::W<XTS_PHYSICAL_ADDRESS_SPEC>;
#[doc = "Field `SPI_XTS_PHYSICAL_ADDRESS` reader - This bits stores the physical-address parameter which will be used in manual encryption calculation. This value should aligned with byte number decided by line-size parameter."]
pub type SPI_XTS_PHYSICAL_ADDRESS_R = crate::FieldReader<u32>;
#[doc = "Field `SPI_XTS_PHYSICAL_ADDRESS` writer - This bits stores the physical-address parameter which will be used in manual encryption calculation. This value should aligned with byte number decided by line-size parameter."]
pub type SPI_XTS_PHYSICAL_ADDRESS_W<'a, REG> = crate::FieldWriter<'a, REG, 26, u32>;
impl R {
    #[doc = "Bits 0:25 - This bits stores the physical-address parameter which will be used in manual encryption calculation. This value should aligned with byte number decided by line-size parameter."]
    #[inline(always)]
    pub fn spi_xts_physical_address(&self) -> SPI_XTS_PHYSICAL_ADDRESS_R {
        SPI_XTS_PHYSICAL_ADDRESS_R::new(self.bits & 0x03ff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("XTS_PHYSICAL_ADDRESS")
            .field("spi_xts_physical_address", &self.spi_xts_physical_address())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:25 - This bits stores the physical-address parameter which will be used in manual encryption calculation. This value should aligned with byte number decided by line-size parameter."]
    #[inline(always)]
    pub fn spi_xts_physical_address(
        &mut self,
    ) -> SPI_XTS_PHYSICAL_ADDRESS_W<'_, XTS_PHYSICAL_ADDRESS_SPEC> {
        SPI_XTS_PHYSICAL_ADDRESS_W::new(self, 0)
    }
}
#[doc = "Manual Encryption physical address register\n\nYou can [`read`](crate::Reg::read) this register and get [`xts_physical_address::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`xts_physical_address::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct XTS_PHYSICAL_ADDRESS_SPEC;
impl crate::RegisterSpec for XTS_PHYSICAL_ADDRESS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`xts_physical_address::R`](R) reader structure"]
impl crate::Readable for XTS_PHYSICAL_ADDRESS_SPEC {}
#[doc = "`write(|w| ..)` method takes [`xts_physical_address::W`](W) writer structure"]
impl crate::Writable for XTS_PHYSICAL_ADDRESS_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets XTS_PHYSICAL_ADDRESS to value 0"]
impl crate::Resettable for XTS_PHYSICAL_ADDRESS_SPEC {}
