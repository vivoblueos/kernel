#[doc = "Register `CACHE_SYNC_CTRL` reader"]
pub type R = crate::R<CACHE_SYNC_CTRL_SPEC>;
#[doc = "Register `CACHE_SYNC_CTRL` writer"]
pub type W = crate::W<CACHE_SYNC_CTRL_SPEC>;
#[doc = "Field `CACHE_INVALIDATE_ENA` reader - The bit is used to enable invalidate operation. It will be cleared by hardware after invalidate operation done. Note that this bit and the other sync-bits (clean_ena, writeback_ena, writeback_invalidate_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
pub type CACHE_INVALIDATE_ENA_R = crate::BitReader;
#[doc = "Field `CACHE_INVALIDATE_ENA` writer - The bit is used to enable invalidate operation. It will be cleared by hardware after invalidate operation done. Note that this bit and the other sync-bits (clean_ena, writeback_ena, writeback_invalidate_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
pub type CACHE_INVALIDATE_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CACHE_CLEAN_ENA` reader - The bit is used to enable clean operation. It will be cleared by hardware after clean operation done. Note that this bit and the other sync-bits (invalidate_ena, writeback_ena, writeback_invalidate_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
pub type CACHE_CLEAN_ENA_R = crate::BitReader;
#[doc = "Field `CACHE_CLEAN_ENA` writer - The bit is used to enable clean operation. It will be cleared by hardware after clean operation done. Note that this bit and the other sync-bits (invalidate_ena, writeback_ena, writeback_invalidate_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
pub type CACHE_CLEAN_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CACHE_WRITEBACK_ENA` reader - The bit is used to enable writeback operation. It will be cleared by hardware after writeback operation done. Note that this bit and the other sync-bits (invalidate_ena, clean_ena, writeback_invalidate_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
pub type CACHE_WRITEBACK_ENA_R = crate::BitReader;
#[doc = "Field `CACHE_WRITEBACK_ENA` writer - The bit is used to enable writeback operation. It will be cleared by hardware after writeback operation done. Note that this bit and the other sync-bits (invalidate_ena, clean_ena, writeback_invalidate_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
pub type CACHE_WRITEBACK_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CACHE_WRITEBACK_INVALIDATE_ENA` reader - The bit is used to enable writeback-invalidate operation. It will be cleared by hardware after writeback-invalidate operation done. Note that this bit and the other sync-bits (invalidate_ena, clean_ena, writeback_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
pub type CACHE_WRITEBACK_INVALIDATE_ENA_R = crate::BitReader;
#[doc = "Field `CACHE_WRITEBACK_INVALIDATE_ENA` writer - The bit is used to enable writeback-invalidate operation. It will be cleared by hardware after writeback-invalidate operation done. Note that this bit and the other sync-bits (invalidate_ena, clean_ena, writeback_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
pub type CACHE_WRITEBACK_INVALIDATE_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CACHE_SYNC_DONE` reader - The bit is used to indicate whether sync operation (invalidate, clean, writeback, writeback_invalidate) is finished or not. 0: not finished. 1: finished."]
pub type CACHE_SYNC_DONE_R = crate::BitReader;
#[doc = "Field `CACHE_SYNC_RGID` reader - The bit is used to set the gid of cache sync operation (invalidate, clean, writeback, writeback_invalidate)"]
pub type CACHE_SYNC_RGID_R = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - The bit is used to enable invalidate operation. It will be cleared by hardware after invalidate operation done. Note that this bit and the other sync-bits (clean_ena, writeback_ena, writeback_invalidate_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
    #[inline(always)]
    pub fn cache_invalidate_ena(&self) -> CACHE_INVALIDATE_ENA_R {
        CACHE_INVALIDATE_ENA_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to enable clean operation. It will be cleared by hardware after clean operation done. Note that this bit and the other sync-bits (invalidate_ena, writeback_ena, writeback_invalidate_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
    #[inline(always)]
    pub fn cache_clean_ena(&self) -> CACHE_CLEAN_ENA_R {
        CACHE_CLEAN_ENA_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The bit is used to enable writeback operation. It will be cleared by hardware after writeback operation done. Note that this bit and the other sync-bits (invalidate_ena, clean_ena, writeback_invalidate_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
    #[inline(always)]
    pub fn cache_writeback_ena(&self) -> CACHE_WRITEBACK_ENA_R {
        CACHE_WRITEBACK_ENA_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The bit is used to enable writeback-invalidate operation. It will be cleared by hardware after writeback-invalidate operation done. Note that this bit and the other sync-bits (invalidate_ena, clean_ena, writeback_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
    #[inline(always)]
    pub fn cache_writeback_invalidate_ena(&self) -> CACHE_WRITEBACK_INVALIDATE_ENA_R {
        CACHE_WRITEBACK_INVALIDATE_ENA_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The bit is used to indicate whether sync operation (invalidate, clean, writeback, writeback_invalidate) is finished or not. 0: not finished. 1: finished."]
    #[inline(always)]
    pub fn cache_sync_done(&self) -> CACHE_SYNC_DONE_R {
        CACHE_SYNC_DONE_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bits 5:8 - The bit is used to set the gid of cache sync operation (invalidate, clean, writeback, writeback_invalidate)"]
    #[inline(always)]
    pub fn cache_sync_rgid(&self) -> CACHE_SYNC_RGID_R {
        CACHE_SYNC_RGID_R::new(((self.bits >> 5) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_SYNC_CTRL")
            .field("cache_invalidate_ena", &self.cache_invalidate_ena())
            .field("cache_clean_ena", &self.cache_clean_ena())
            .field("cache_writeback_ena", &self.cache_writeback_ena())
            .field(
                "cache_writeback_invalidate_ena",
                &self.cache_writeback_invalidate_ena(),
            )
            .field("cache_sync_done", &self.cache_sync_done())
            .field("cache_sync_rgid", &self.cache_sync_rgid())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to enable invalidate operation. It will be cleared by hardware after invalidate operation done. Note that this bit and the other sync-bits (clean_ena, writeback_ena, writeback_invalidate_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
    #[inline(always)]
    pub fn cache_invalidate_ena(&mut self) -> CACHE_INVALIDATE_ENA_W<'_, CACHE_SYNC_CTRL_SPEC> {
        CACHE_INVALIDATE_ENA_W::new(self, 0)
    }
    #[doc = "Bit 1 - The bit is used to enable clean operation. It will be cleared by hardware after clean operation done. Note that this bit and the other sync-bits (invalidate_ena, writeback_ena, writeback_invalidate_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
    #[inline(always)]
    pub fn cache_clean_ena(&mut self) -> CACHE_CLEAN_ENA_W<'_, CACHE_SYNC_CTRL_SPEC> {
        CACHE_CLEAN_ENA_W::new(self, 1)
    }
    #[doc = "Bit 2 - The bit is used to enable writeback operation. It will be cleared by hardware after writeback operation done. Note that this bit and the other sync-bits (invalidate_ena, clean_ena, writeback_invalidate_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
    #[inline(always)]
    pub fn cache_writeback_ena(&mut self) -> CACHE_WRITEBACK_ENA_W<'_, CACHE_SYNC_CTRL_SPEC> {
        CACHE_WRITEBACK_ENA_W::new(self, 2)
    }
    #[doc = "Bit 3 - The bit is used to enable writeback-invalidate operation. It will be cleared by hardware after writeback-invalidate operation done. Note that this bit and the other sync-bits (invalidate_ena, clean_ena, writeback_ena) are mutually exclusive, that is, those bits can not be set to 1 at the same time."]
    #[inline(always)]
    pub fn cache_writeback_invalidate_ena(
        &mut self,
    ) -> CACHE_WRITEBACK_INVALIDATE_ENA_W<'_, CACHE_SYNC_CTRL_SPEC> {
        CACHE_WRITEBACK_INVALIDATE_ENA_W::new(self, 3)
    }
}
#[doc = "Sync-class operation control register\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_sync_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_sync_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_SYNC_CTRL_SPEC;
impl crate::RegisterSpec for CACHE_SYNC_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_sync_ctrl::R`](R) reader structure"]
impl crate::Readable for CACHE_SYNC_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cache_sync_ctrl::W`](W) writer structure"]
impl crate::Writable for CACHE_SYNC_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CACHE_SYNC_CTRL to value 0x01"]
impl crate::Resettable for CACHE_SYNC_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
