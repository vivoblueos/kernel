#[doc = "Register `PHYSICAL_ADDRESS` reader"]
pub type R = crate::R<PHYSICAL_ADDRESS_SPEC>;
#[doc = "Register `PHYSICAL_ADDRESS` writer"]
pub type W = crate::W<PHYSICAL_ADDRESS_SPEC>;
#[doc = "Field `PHYSICAL_ADDRESS` reader - Those bits stores the physical address. If linesize is 16-byte, the physical address should be aligned of 16 bytes. If linesize is 32-byte, the physical address should be aligned of 32 bytes."]
pub type PHYSICAL_ADDRESS_R = crate::FieldReader<u32>;
#[doc = "Field `PHYSICAL_ADDRESS` writer - Those bits stores the physical address. If linesize is 16-byte, the physical address should be aligned of 16 bytes. If linesize is 32-byte, the physical address should be aligned of 32 bytes."]
pub type PHYSICAL_ADDRESS_W<'a, REG> = crate::FieldWriter<'a, REG, 30, u32>;
impl R {
    #[doc = "Bits 0:29 - Those bits stores the physical address. If linesize is 16-byte, the physical address should be aligned of 16 bytes. If linesize is 32-byte, the physical address should be aligned of 32 bytes."]
    #[inline(always)]
    pub fn physical_address(&self) -> PHYSICAL_ADDRESS_R {
        PHYSICAL_ADDRESS_R::new(self.bits & 0x3fff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PHYSICAL_ADDRESS")
            .field("physical_address", &self.physical_address())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:29 - Those bits stores the physical address. If linesize is 16-byte, the physical address should be aligned of 16 bytes. If linesize is 32-byte, the physical address should be aligned of 32 bytes."]
    #[inline(always)]
    pub fn physical_address(&mut self) -> PHYSICAL_ADDRESS_W<'_, PHYSICAL_ADDRESS_SPEC> {
        PHYSICAL_ADDRESS_W::new(self, 0)
    }
}
#[doc = "XTS-AES physical address register\n\nYou can [`read`](crate::Reg::read) this register and get [`physical_address::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`physical_address::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PHYSICAL_ADDRESS_SPEC;
impl crate::RegisterSpec for PHYSICAL_ADDRESS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`physical_address::R`](R) reader structure"]
impl crate::Readable for PHYSICAL_ADDRESS_SPEC {}
#[doc = "`write(|w| ..)` method takes [`physical_address::W`](W) writer structure"]
impl crate::Writable for PHYSICAL_ADDRESS_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PHYSICAL_ADDRESS to value 0"]
impl crate::Resettable for PHYSICAL_ADDRESS_SPEC {}
