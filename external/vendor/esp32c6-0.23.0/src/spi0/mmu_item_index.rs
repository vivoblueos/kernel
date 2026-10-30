#[doc = "Register `MMU_ITEM_INDEX` reader"]
pub type R = crate::R<MMU_ITEM_INDEX_SPEC>;
#[doc = "Register `MMU_ITEM_INDEX` writer"]
pub type W = crate::W<MMU_ITEM_INDEX_SPEC>;
#[doc = "Field `SPI_MMU_ITEM_INDEX` reader - MSPI-MMU item index"]
pub type SPI_MMU_ITEM_INDEX_R = crate::FieldReader<u32>;
#[doc = "Field `SPI_MMU_ITEM_INDEX` writer - MSPI-MMU item index"]
pub type SPI_MMU_ITEM_INDEX_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - MSPI-MMU item index"]
    #[inline(always)]
    pub fn spi_mmu_item_index(&self) -> SPI_MMU_ITEM_INDEX_R {
        SPI_MMU_ITEM_INDEX_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MMU_ITEM_INDEX")
            .field("spi_mmu_item_index", &self.spi_mmu_item_index())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - MSPI-MMU item index"]
    #[inline(always)]
    pub fn spi_mmu_item_index(&mut self) -> SPI_MMU_ITEM_INDEX_W<'_, MMU_ITEM_INDEX_SPEC> {
        SPI_MMU_ITEM_INDEX_W::new(self, 0)
    }
}
#[doc = "MSPI-MMU item index register\n\nYou can [`read`](crate::Reg::read) this register and get [`mmu_item_index::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mmu_item_index::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MMU_ITEM_INDEX_SPEC;
impl crate::RegisterSpec for MMU_ITEM_INDEX_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mmu_item_index::R`](R) reader structure"]
impl crate::Readable for MMU_ITEM_INDEX_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mmu_item_index::W`](W) writer structure"]
impl crate::Writable for MMU_ITEM_INDEX_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MMU_ITEM_INDEX to value 0"]
impl crate::Resettable for MMU_ITEM_INDEX_SPEC {}
