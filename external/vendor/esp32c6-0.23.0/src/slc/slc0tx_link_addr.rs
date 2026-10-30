#[doc = "Register `SLC0TX_LINK_ADDR` reader"]
pub type R = crate::R<SLC0TX_LINK_ADDR_SPEC>;
#[doc = "Register `SLC0TX_LINK_ADDR` writer"]
pub type W = crate::W<SLC0TX_LINK_ADDR_SPEC>;
#[doc = "Field `SDIO_SLC0_TXLINK_ADDR` reader - Configures SLC0 TX linked list initial address."]
pub type SDIO_SLC0_TXLINK_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `SDIO_SLC0_TXLINK_ADDR` writer - Configures SLC0 TX linked list initial address."]
pub type SDIO_SLC0_TXLINK_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Configures SLC0 TX linked list initial address."]
    #[inline(always)]
    pub fn sdio_slc0_txlink_addr(&self) -> SDIO_SLC0_TXLINK_ADDR_R {
        SDIO_SLC0_TXLINK_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLC0TX_LINK_ADDR")
            .field("sdio_slc0_txlink_addr", &self.sdio_slc0_txlink_addr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Configures SLC0 TX linked list initial address."]
    #[inline(always)]
    pub fn sdio_slc0_txlink_addr(&mut self) -> SDIO_SLC0_TXLINK_ADDR_W<'_, SLC0TX_LINK_ADDR_SPEC> {
        SDIO_SLC0_TXLINK_ADDR_W::new(self, 0)
    }
}
#[doc = "SLC0 TX linked list address\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0tx_link_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0tx_link_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLC0TX_LINK_ADDR_SPEC;
impl crate::RegisterSpec for SLC0TX_LINK_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slc0tx_link_addr::R`](R) reader structure"]
impl crate::Readable for SLC0TX_LINK_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slc0tx_link_addr::W`](W) writer structure"]
impl crate::Writable for SLC0TX_LINK_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLC0TX_LINK_ADDR to value 0"]
impl crate::Resettable for SLC0TX_LINK_ADDR_SPEC {}
