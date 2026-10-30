#[doc = "Register `CRCPOLY` reader"]
pub type R = crate::R<CrcpolySpec>;
#[doc = "Register `CRCPOLY` writer"]
pub type W = crate::W<CrcpolySpec>;
#[doc = "Field `CRCPOLY` reader - CRC polynomial register"]
pub type CrcpolyR = crate::FieldReader<u16>;
#[doc = "Field `CRCPOLY` writer - CRC polynomial register"]
pub type CrcpolyW<'a, REG> = crate::FieldWriterSafe<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - CRC polynomial register"]
    #[inline(always)]
    pub fn crcpoly(&self) -> CrcpolyR {
        CrcpolyR::new((self.bits & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - CRC polynomial register"]
    #[inline(always)]
    #[must_use]
    pub fn crcpoly(&mut self) -> CrcpolyW<CrcpolySpec> {
        CrcpolyW::new(self, 0)
    }
}
#[doc = "CRC polynomial register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`crcpoly::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`crcpoly::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CrcpolySpec;
impl crate::RegisterSpec for CrcpolySpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`crcpoly::R`](R) reader structure"]
impl crate::Readable for CrcpolySpec {}
#[doc = "`write(|w| ..)` method takes [`crcpoly::W`](W) writer structure"]
impl crate::Writable for CrcpolySpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CRCPOLY to value 0x07"]
impl crate::Resettable for CrcpolySpec {
    const RESET_VALUE: u32 = 0x07;
}
