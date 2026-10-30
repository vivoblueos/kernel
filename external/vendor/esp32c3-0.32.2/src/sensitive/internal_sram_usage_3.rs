#[doc = "Register `INTERNAL_SRAM_USAGE_3` reader"]
pub type R = crate::R<INTERNAL_SRAM_USAGE_3_SPEC>;
#[doc = "Register `INTERNAL_SRAM_USAGE_3` writer"]
pub type W = crate::W<INTERNAL_SRAM_USAGE_3_SPEC>;
#[doc = "Field `INTERNAL_SRAM_USAGE_MAC_DUMP_SRAM` reader - internal_sram_usage_mac_dump_sram"]
pub type INTERNAL_SRAM_USAGE_MAC_DUMP_SRAM_R = crate::FieldReader;
#[doc = "Field `INTERNAL_SRAM_USAGE_MAC_DUMP_SRAM` writer - internal_sram_usage_mac_dump_sram"]
pub type INTERNAL_SRAM_USAGE_MAC_DUMP_SRAM_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `INTERNAL_SRAM_ALLOC_MAC_DUMP` reader - internal_sram_alloc_mac_dump"]
pub type INTERNAL_SRAM_ALLOC_MAC_DUMP_R = crate::BitReader;
#[doc = "Field `INTERNAL_SRAM_ALLOC_MAC_DUMP` writer - internal_sram_alloc_mac_dump"]
pub type INTERNAL_SRAM_ALLOC_MAC_DUMP_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:2 - internal_sram_usage_mac_dump_sram"]
    #[inline(always)]
    pub fn internal_sram_usage_mac_dump_sram(&self) -> INTERNAL_SRAM_USAGE_MAC_DUMP_SRAM_R {
        INTERNAL_SRAM_USAGE_MAC_DUMP_SRAM_R::new((self.bits & 7) as u8)
    }
    #[doc = "Bit 3 - internal_sram_alloc_mac_dump"]
    #[inline(always)]
    pub fn internal_sram_alloc_mac_dump(&self) -> INTERNAL_SRAM_ALLOC_MAC_DUMP_R {
        INTERNAL_SRAM_ALLOC_MAC_DUMP_R::new(((self.bits >> 3) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INTERNAL_SRAM_USAGE_3")
            .field(
                "internal_sram_usage_mac_dump_sram",
                &self.internal_sram_usage_mac_dump_sram(),
            )
            .field(
                "internal_sram_alloc_mac_dump",
                &self.internal_sram_alloc_mac_dump(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:2 - internal_sram_usage_mac_dump_sram"]
    #[inline(always)]
    pub fn internal_sram_usage_mac_dump_sram(
        &mut self,
    ) -> INTERNAL_SRAM_USAGE_MAC_DUMP_SRAM_W<'_, INTERNAL_SRAM_USAGE_3_SPEC> {
        INTERNAL_SRAM_USAGE_MAC_DUMP_SRAM_W::new(self, 0)
    }
    #[doc = "Bit 3 - internal_sram_alloc_mac_dump"]
    #[inline(always)]
    pub fn internal_sram_alloc_mac_dump(
        &mut self,
    ) -> INTERNAL_SRAM_ALLOC_MAC_DUMP_W<'_, INTERNAL_SRAM_USAGE_3_SPEC> {
        INTERNAL_SRAM_ALLOC_MAC_DUMP_W::new(self, 3)
    }
}
#[doc = "SENSITIVE_INTERNAL_SRAM_USAGE_3_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`internal_sram_usage_3::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`internal_sram_usage_3::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INTERNAL_SRAM_USAGE_3_SPEC;
impl crate::RegisterSpec for INTERNAL_SRAM_USAGE_3_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`internal_sram_usage_3::R`](R) reader structure"]
impl crate::Readable for INTERNAL_SRAM_USAGE_3_SPEC {}
#[doc = "`write(|w| ..)` method takes [`internal_sram_usage_3::W`](W) writer structure"]
impl crate::Writable for INTERNAL_SRAM_USAGE_3_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INTERNAL_SRAM_USAGE_3 to value 0"]
impl crate::Resettable for INTERNAL_SRAM_USAGE_3_SPEC {}
