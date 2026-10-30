#[doc = "Register `ICACHE_SYNC_CTRL` reader"]
pub type R = crate::R<ICACHE_SYNC_CTRL_SPEC>;
#[doc = "Register `ICACHE_SYNC_CTRL` writer"]
pub type W = crate::W<ICACHE_SYNC_CTRL_SPEC>;
#[doc = "Field `ICACHE_INVALIDATE_ENA` reader - The bit is used to enable invalidate operation. It will be cleared by hardware after invalidate operation done."]
pub type ICACHE_INVALIDATE_ENA_R = crate::BitReader;
#[doc = "Field `ICACHE_INVALIDATE_ENA` writer - The bit is used to enable invalidate operation. It will be cleared by hardware after invalidate operation done."]
pub type ICACHE_INVALIDATE_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ICACHE_SYNC_DONE` reader - The bit is used to indicate invalidate operation is finished."]
pub type ICACHE_SYNC_DONE_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The bit is used to enable invalidate operation. It will be cleared by hardware after invalidate operation done."]
    #[inline(always)]
    pub fn icache_invalidate_ena(&self) -> ICACHE_INVALIDATE_ENA_R {
        ICACHE_INVALIDATE_ENA_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to indicate invalidate operation is finished."]
    #[inline(always)]
    pub fn icache_sync_done(&self) -> ICACHE_SYNC_DONE_R {
        ICACHE_SYNC_DONE_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ICACHE_SYNC_CTRL")
            .field("icache_invalidate_ena", &self.icache_invalidate_ena())
            .field("icache_sync_done", &self.icache_sync_done())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to enable invalidate operation. It will be cleared by hardware after invalidate operation done."]
    #[inline(always)]
    pub fn icache_invalidate_ena(&mut self) -> ICACHE_INVALIDATE_ENA_W<'_, ICACHE_SYNC_CTRL_SPEC> {
        ICACHE_INVALIDATE_ENA_W::new(self, 0)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_sync_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_sync_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ICACHE_SYNC_CTRL_SPEC;
impl crate::RegisterSpec for ICACHE_SYNC_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`icache_sync_ctrl::R`](R) reader structure"]
impl crate::Readable for ICACHE_SYNC_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`icache_sync_ctrl::W`](W) writer structure"]
impl crate::Writable for ICACHE_SYNC_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ICACHE_SYNC_CTRL to value 0x01"]
impl crate::Resettable for ICACHE_SYNC_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
