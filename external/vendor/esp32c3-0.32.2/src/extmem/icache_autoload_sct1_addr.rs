#[doc = "Register `ICACHE_AUTOLOAD_SCT1_ADDR` reader"]
pub type R = crate::R<ICACHE_AUTOLOAD_SCT1_ADDR_SPEC>;
#[doc = "Register `ICACHE_AUTOLOAD_SCT1_ADDR` writer"]
pub type W = crate::W<ICACHE_AUTOLOAD_SCT1_ADDR_SPEC>;
#[doc = "Field `ICACHE_AUTOLOAD_SCT1_ADDR` reader - The bits are used to configure the start virtual address of the second section for autoload operation. It should be combined with icache_autoload_sct1_ena."]
pub type ICACHE_AUTOLOAD_SCT1_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `ICACHE_AUTOLOAD_SCT1_ADDR` writer - The bits are used to configure the start virtual address of the second section for autoload operation. It should be combined with icache_autoload_sct1_ena."]
pub type ICACHE_AUTOLOAD_SCT1_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - The bits are used to configure the start virtual address of the second section for autoload operation. It should be combined with icache_autoload_sct1_ena."]
    #[inline(always)]
    pub fn icache_autoload_sct1_addr(&self) -> ICACHE_AUTOLOAD_SCT1_ADDR_R {
        ICACHE_AUTOLOAD_SCT1_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ICACHE_AUTOLOAD_SCT1_ADDR")
            .field(
                "icache_autoload_sct1_addr",
                &self.icache_autoload_sct1_addr(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - The bits are used to configure the start virtual address of the second section for autoload operation. It should be combined with icache_autoload_sct1_ena."]
    #[inline(always)]
    pub fn icache_autoload_sct1_addr(
        &mut self,
    ) -> ICACHE_AUTOLOAD_SCT1_ADDR_W<'_, ICACHE_AUTOLOAD_SCT1_ADDR_SPEC> {
        ICACHE_AUTOLOAD_SCT1_ADDR_W::new(self, 0)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_autoload_sct1_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_autoload_sct1_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ICACHE_AUTOLOAD_SCT1_ADDR_SPEC;
impl crate::RegisterSpec for ICACHE_AUTOLOAD_SCT1_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`icache_autoload_sct1_addr::R`](R) reader structure"]
impl crate::Readable for ICACHE_AUTOLOAD_SCT1_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`icache_autoload_sct1_addr::W`](W) writer structure"]
impl crate::Writable for ICACHE_AUTOLOAD_SCT1_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ICACHE_AUTOLOAD_SCT1_ADDR to value 0"]
impl crate::Resettable for ICACHE_AUTOLOAD_SCT1_ADDR_SPEC {}
