#[doc = "Register `XTS_LINESIZE` reader"]
pub type R = crate::R<XTS_LINESIZE_SPEC>;
#[doc = "Register `XTS_LINESIZE` writer"]
pub type W = crate::W<XTS_LINESIZE_SPEC>;
#[doc = "Field `SPI_XTS_LINESIZE` reader - This bits stores the line-size parameter which will be used in manual encryption calculation. It decides how many bytes will be encrypted one time. 0: 16-bytes, 1: 32-bytes, 2: 64-bytes, 3:reserved."]
pub type SPI_XTS_LINESIZE_R = crate::FieldReader;
#[doc = "Field `SPI_XTS_LINESIZE` writer - This bits stores the line-size parameter which will be used in manual encryption calculation. It decides how many bytes will be encrypted one time. 0: 16-bytes, 1: 32-bytes, 2: 64-bytes, 3:reserved."]
pub type SPI_XTS_LINESIZE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - This bits stores the line-size parameter which will be used in manual encryption calculation. It decides how many bytes will be encrypted one time. 0: 16-bytes, 1: 32-bytes, 2: 64-bytes, 3:reserved."]
    #[inline(always)]
    pub fn spi_xts_linesize(&self) -> SPI_XTS_LINESIZE_R {
        SPI_XTS_LINESIZE_R::new((self.bits & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("XTS_LINESIZE")
            .field("spi_xts_linesize", &self.spi_xts_linesize())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - This bits stores the line-size parameter which will be used in manual encryption calculation. It decides how many bytes will be encrypted one time. 0: 16-bytes, 1: 32-bytes, 2: 64-bytes, 3:reserved."]
    #[inline(always)]
    pub fn spi_xts_linesize(&mut self) -> SPI_XTS_LINESIZE_W<'_, XTS_LINESIZE_SPEC> {
        SPI_XTS_LINESIZE_W::new(self, 0)
    }
}
#[doc = "Manual Encryption Line-Size register\n\nYou can [`read`](crate::Reg::read) this register and get [`xts_linesize::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`xts_linesize::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct XTS_LINESIZE_SPEC;
impl crate::RegisterSpec for XTS_LINESIZE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`xts_linesize::R`](R) reader structure"]
impl crate::Readable for XTS_LINESIZE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`xts_linesize::W`](W) writer structure"]
impl crate::Writable for XTS_LINESIZE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets XTS_LINESIZE to value 0"]
impl crate::Resettable for XTS_LINESIZE_SPEC {}
