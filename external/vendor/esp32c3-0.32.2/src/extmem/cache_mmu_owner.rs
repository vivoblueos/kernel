#[doc = "Register `CACHE_MMU_OWNER` reader"]
pub type R = crate::R<CACHE_MMU_OWNER_SPEC>;
#[doc = "Register `CACHE_MMU_OWNER` writer"]
pub type W = crate::W<CACHE_MMU_OWNER_SPEC>;
#[doc = "Field `CACHE_MMU_OWNER` reader - The bits are used to specify the owner of MMU.bit0/bit2: ibus, bit1/bit3: dbus"]
pub type CACHE_MMU_OWNER_R = crate::FieldReader;
#[doc = "Field `CACHE_MMU_OWNER` writer - The bits are used to specify the owner of MMU.bit0/bit2: ibus, bit1/bit3: dbus"]
pub type CACHE_MMU_OWNER_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3 - The bits are used to specify the owner of MMU.bit0/bit2: ibus, bit1/bit3: dbus"]
    #[inline(always)]
    pub fn cache_mmu_owner(&self) -> CACHE_MMU_OWNER_R {
        CACHE_MMU_OWNER_R::new((self.bits & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_MMU_OWNER")
            .field("cache_mmu_owner", &self.cache_mmu_owner())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3 - The bits are used to specify the owner of MMU.bit0/bit2: ibus, bit1/bit3: dbus"]
    #[inline(always)]
    pub fn cache_mmu_owner(&mut self) -> CACHE_MMU_OWNER_W<'_, CACHE_MMU_OWNER_SPEC> {
        CACHE_MMU_OWNER_W::new(self, 0)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_mmu_owner::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_mmu_owner::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_MMU_OWNER_SPEC;
impl crate::RegisterSpec for CACHE_MMU_OWNER_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_mmu_owner::R`](R) reader structure"]
impl crate::Readable for CACHE_MMU_OWNER_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cache_mmu_owner::W`](W) writer structure"]
impl crate::Writable for CACHE_MMU_OWNER_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CACHE_MMU_OWNER to value 0"]
impl crate::Resettable for CACHE_MMU_OWNER_SPEC {}
