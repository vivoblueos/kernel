#[doc = "Register `MOSI_DLEN` reader"]
pub type R = crate::R<MOSI_DLEN_SPEC>;
#[doc = "Register `MOSI_DLEN` writer"]
pub type W = crate::W<MOSI_DLEN_SPEC>;
#[doc = "Field `USR_MOSI_DBITLEN` reader - The length in bits of write-data. The register value shall be (bit_num-1)."]
pub type USR_MOSI_DBITLEN_R = crate::FieldReader<u16>;
#[doc = "Field `USR_MOSI_DBITLEN` writer - The length in bits of write-data. The register value shall be (bit_num-1)."]
pub type USR_MOSI_DBITLEN_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
impl R {
    #[doc = "Bits 0:9 - The length in bits of write-data. The register value shall be (bit_num-1)."]
    #[inline(always)]
    pub fn usr_mosi_dbitlen(&self) -> USR_MOSI_DBITLEN_R {
        USR_MOSI_DBITLEN_R::new((self.bits & 0x03ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MOSI_DLEN")
            .field("usr_mosi_dbitlen", &self.usr_mosi_dbitlen())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:9 - The length in bits of write-data. The register value shall be (bit_num-1)."]
    #[inline(always)]
    pub fn usr_mosi_dbitlen(&mut self) -> USR_MOSI_DBITLEN_W<'_, MOSI_DLEN_SPEC> {
        USR_MOSI_DBITLEN_W::new(self, 0)
    }
}
#[doc = "SPI1 send data bit length control register.\n\nYou can [`read`](crate::Reg::read) this register and get [`mosi_dlen::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mosi_dlen::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MOSI_DLEN_SPEC;
impl crate::RegisterSpec for MOSI_DLEN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mosi_dlen::R`](R) reader structure"]
impl crate::Readable for MOSI_DLEN_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mosi_dlen::W`](W) writer structure"]
impl crate::Writable for MOSI_DLEN_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MOSI_DLEN to value 0"]
impl crate::Resettable for MOSI_DLEN_SPEC {}
