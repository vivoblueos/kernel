#[doc = "Register `CACHE_LOCK_CTRL` reader"]
pub type R = crate::R<CACHE_LOCK_CTRL_SPEC>;
#[doc = "Register `CACHE_LOCK_CTRL` writer"]
pub type W = crate::W<CACHE_LOCK_CTRL_SPEC>;
#[doc = "Field `CACHE_LOCK_ENA` reader - The bit is used to enable lock operation. It will be cleared by hardware after lock operation done"]
pub type CACHE_LOCK_ENA_R = crate::BitReader;
#[doc = "Field `CACHE_LOCK_ENA` writer - The bit is used to enable lock operation. It will be cleared by hardware after lock operation done"]
pub type CACHE_LOCK_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CACHE_UNLOCK_ENA` reader - The bit is used to enable unlock operation. It will be cleared by hardware after unlock operation done"]
pub type CACHE_UNLOCK_ENA_R = crate::BitReader;
#[doc = "Field `CACHE_UNLOCK_ENA` writer - The bit is used to enable unlock operation. It will be cleared by hardware after unlock operation done"]
pub type CACHE_UNLOCK_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CACHE_LOCK_DONE` reader - The bit is used to indicate whether unlock/lock operation is finished or not. 0: not finished. 1: finished."]
pub type CACHE_LOCK_DONE_R = crate::BitReader;
#[doc = "Field `CACHE_LOCK_RGID` reader - The bit is used to set the gid of cache lock/unlock."]
pub type CACHE_LOCK_RGID_R = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - The bit is used to enable lock operation. It will be cleared by hardware after lock operation done"]
    #[inline(always)]
    pub fn cache_lock_ena(&self) -> CACHE_LOCK_ENA_R {
        CACHE_LOCK_ENA_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to enable unlock operation. It will be cleared by hardware after unlock operation done"]
    #[inline(always)]
    pub fn cache_unlock_ena(&self) -> CACHE_UNLOCK_ENA_R {
        CACHE_UNLOCK_ENA_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The bit is used to indicate whether unlock/lock operation is finished or not. 0: not finished. 1: finished."]
    #[inline(always)]
    pub fn cache_lock_done(&self) -> CACHE_LOCK_DONE_R {
        CACHE_LOCK_DONE_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bits 3:6 - The bit is used to set the gid of cache lock/unlock."]
    #[inline(always)]
    pub fn cache_lock_rgid(&self) -> CACHE_LOCK_RGID_R {
        CACHE_LOCK_RGID_R::new(((self.bits >> 3) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_LOCK_CTRL")
            .field("cache_lock_ena", &self.cache_lock_ena())
            .field("cache_unlock_ena", &self.cache_unlock_ena())
            .field("cache_lock_done", &self.cache_lock_done())
            .field("cache_lock_rgid", &self.cache_lock_rgid())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to enable lock operation. It will be cleared by hardware after lock operation done"]
    #[inline(always)]
    pub fn cache_lock_ena(&mut self) -> CACHE_LOCK_ENA_W<'_, CACHE_LOCK_CTRL_SPEC> {
        CACHE_LOCK_ENA_W::new(self, 0)
    }
    #[doc = "Bit 1 - The bit is used to enable unlock operation. It will be cleared by hardware after unlock operation done"]
    #[inline(always)]
    pub fn cache_unlock_ena(&mut self) -> CACHE_UNLOCK_ENA_W<'_, CACHE_LOCK_CTRL_SPEC> {
        CACHE_UNLOCK_ENA_W::new(self, 1)
    }
}
#[doc = "Lock-class (manual lock) operation control register\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_lock_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_lock_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_LOCK_CTRL_SPEC;
impl crate::RegisterSpec for CACHE_LOCK_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_lock_ctrl::R`](R) reader structure"]
impl crate::Readable for CACHE_LOCK_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cache_lock_ctrl::W`](W) writer structure"]
impl crate::Writable for CACHE_LOCK_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CACHE_LOCK_CTRL to value 0x04"]
impl crate::Resettable for CACHE_LOCK_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x04;
}
