#[doc = "Register `L1_CACHE_FREEZE_CTRL` reader"]
pub type R = crate::R<L1_CACHE_FREEZE_CTRL_SPEC>;
#[doc = "Register `L1_CACHE_FREEZE_CTRL` writer"]
pub type W = crate::W<L1_CACHE_FREEZE_CTRL_SPEC>;
#[doc = "Field `L1_ICACHE0_FREEZE_EN` reader - The bit is used to enable freeze operation on L1-ICache0. It can be cleared by software."]
pub type L1_ICACHE0_FREEZE_EN_R = crate::BitReader;
#[doc = "Field `L1_ICACHE0_FREEZE_MODE` reader - The bit is used to configure mode of freeze operation L1-ICache0. 0: a miss-access will not stuck. 1: a miss-access will stuck."]
pub type L1_ICACHE0_FREEZE_MODE_R = crate::BitReader;
#[doc = "Field `L1_ICACHE0_FREEZE_DONE` reader - The bit is used to indicate whether freeze operation on L1-ICache0 is finished or not. 0: not finished. 1: finished."]
pub type L1_ICACHE0_FREEZE_DONE_R = crate::BitReader;
#[doc = "Field `L1_ICACHE1_FREEZE_EN` reader - The bit is used to enable freeze operation on L1-ICache1. It can be cleared by software."]
pub type L1_ICACHE1_FREEZE_EN_R = crate::BitReader;
#[doc = "Field `L1_ICACHE1_FREEZE_MODE` reader - The bit is used to configure mode of freeze operation L1-ICache1. 0: a miss-access will not stuck. 1: a miss-access will stuck."]
pub type L1_ICACHE1_FREEZE_MODE_R = crate::BitReader;
#[doc = "Field `L1_ICACHE1_FREEZE_DONE` reader - The bit is used to indicate whether freeze operation on L1-ICache1 is finished or not. 0: not finished. 1: finished."]
pub type L1_ICACHE1_FREEZE_DONE_R = crate::BitReader;
#[doc = "Field `L1_ICACHE2_FREEZE_EN` reader - Reserved"]
pub type L1_ICACHE2_FREEZE_EN_R = crate::BitReader;
#[doc = "Field `L1_ICACHE2_FREEZE_MODE` reader - Reserved"]
pub type L1_ICACHE2_FREEZE_MODE_R = crate::BitReader;
#[doc = "Field `L1_ICACHE2_FREEZE_DONE` reader - Reserved"]
pub type L1_ICACHE2_FREEZE_DONE_R = crate::BitReader;
#[doc = "Field `L1_ICACHE3_FREEZE_EN` reader - Reserved"]
pub type L1_ICACHE3_FREEZE_EN_R = crate::BitReader;
#[doc = "Field `L1_ICACHE3_FREEZE_MODE` reader - Reserved"]
pub type L1_ICACHE3_FREEZE_MODE_R = crate::BitReader;
#[doc = "Field `L1_ICACHE3_FREEZE_DONE` reader - Reserved"]
pub type L1_ICACHE3_FREEZE_DONE_R = crate::BitReader;
#[doc = "Field `L1_CACHE_FREEZE_EN` reader - The bit is used to enable freeze operation on L1-Cache. It can be cleared by software."]
pub type L1_CACHE_FREEZE_EN_R = crate::BitReader;
#[doc = "Field `L1_CACHE_FREEZE_EN` writer - The bit is used to enable freeze operation on L1-Cache. It can be cleared by software."]
pub type L1_CACHE_FREEZE_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_CACHE_FREEZE_MODE` reader - The bit is used to configure mode of freeze operation L1-Cache. 0: a miss-access will not stuck. 1: a miss-access will stuck."]
pub type L1_CACHE_FREEZE_MODE_R = crate::BitReader;
#[doc = "Field `L1_CACHE_FREEZE_MODE` writer - The bit is used to configure mode of freeze operation L1-Cache. 0: a miss-access will not stuck. 1: a miss-access will stuck."]
pub type L1_CACHE_FREEZE_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_CACHE_FREEZE_DONE` reader - The bit is used to indicate whether freeze operation on L1-Cache is finished or not. 0: not finished. 1: finished."]
pub type L1_CACHE_FREEZE_DONE_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The bit is used to enable freeze operation on L1-ICache0. It can be cleared by software."]
    #[inline(always)]
    pub fn l1_icache0_freeze_en(&self) -> L1_ICACHE0_FREEZE_EN_R {
        L1_ICACHE0_FREEZE_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to configure mode of freeze operation L1-ICache0. 0: a miss-access will not stuck. 1: a miss-access will stuck."]
    #[inline(always)]
    pub fn l1_icache0_freeze_mode(&self) -> L1_ICACHE0_FREEZE_MODE_R {
        L1_ICACHE0_FREEZE_MODE_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The bit is used to indicate whether freeze operation on L1-ICache0 is finished or not. 0: not finished. 1: finished."]
    #[inline(always)]
    pub fn l1_icache0_freeze_done(&self) -> L1_ICACHE0_FREEZE_DONE_R {
        L1_ICACHE0_FREEZE_DONE_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 4 - The bit is used to enable freeze operation on L1-ICache1. It can be cleared by software."]
    #[inline(always)]
    pub fn l1_icache1_freeze_en(&self) -> L1_ICACHE1_FREEZE_EN_R {
        L1_ICACHE1_FREEZE_EN_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The bit is used to configure mode of freeze operation L1-ICache1. 0: a miss-access will not stuck. 1: a miss-access will stuck."]
    #[inline(always)]
    pub fn l1_icache1_freeze_mode(&self) -> L1_ICACHE1_FREEZE_MODE_R {
        L1_ICACHE1_FREEZE_MODE_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The bit is used to indicate whether freeze operation on L1-ICache1 is finished or not. 0: not finished. 1: finished."]
    #[inline(always)]
    pub fn l1_icache1_freeze_done(&self) -> L1_ICACHE1_FREEZE_DONE_R {
        L1_ICACHE1_FREEZE_DONE_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 8 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_freeze_en(&self) -> L1_ICACHE2_FREEZE_EN_R {
        L1_ICACHE2_FREEZE_EN_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_freeze_mode(&self) -> L1_ICACHE2_FREEZE_MODE_R {
        L1_ICACHE2_FREEZE_MODE_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_freeze_done(&self) -> L1_ICACHE2_FREEZE_DONE_R {
        L1_ICACHE2_FREEZE_DONE_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 12 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_freeze_en(&self) -> L1_ICACHE3_FREEZE_EN_R {
        L1_ICACHE3_FREEZE_EN_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_freeze_mode(&self) -> L1_ICACHE3_FREEZE_MODE_R {
        L1_ICACHE3_FREEZE_MODE_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_freeze_done(&self) -> L1_ICACHE3_FREEZE_DONE_R {
        L1_ICACHE3_FREEZE_DONE_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 16 - The bit is used to enable freeze operation on L1-Cache. It can be cleared by software."]
    #[inline(always)]
    pub fn l1_cache_freeze_en(&self) -> L1_CACHE_FREEZE_EN_R {
        L1_CACHE_FREEZE_EN_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - The bit is used to configure mode of freeze operation L1-Cache. 0: a miss-access will not stuck. 1: a miss-access will stuck."]
    #[inline(always)]
    pub fn l1_cache_freeze_mode(&self) -> L1_CACHE_FREEZE_MODE_R {
        L1_CACHE_FREEZE_MODE_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - The bit is used to indicate whether freeze operation on L1-Cache is finished or not. 0: not finished. 1: finished."]
    #[inline(always)]
    pub fn l1_cache_freeze_done(&self) -> L1_CACHE_FREEZE_DONE_R {
        L1_CACHE_FREEZE_DONE_R::new(((self.bits >> 18) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_FREEZE_CTRL")
            .field("l1_icache0_freeze_en", &self.l1_icache0_freeze_en())
            .field("l1_icache0_freeze_mode", &self.l1_icache0_freeze_mode())
            .field("l1_icache0_freeze_done", &self.l1_icache0_freeze_done())
            .field("l1_icache1_freeze_en", &self.l1_icache1_freeze_en())
            .field("l1_icache1_freeze_mode", &self.l1_icache1_freeze_mode())
            .field("l1_icache1_freeze_done", &self.l1_icache1_freeze_done())
            .field("l1_icache2_freeze_en", &self.l1_icache2_freeze_en())
            .field("l1_icache2_freeze_mode", &self.l1_icache2_freeze_mode())
            .field("l1_icache2_freeze_done", &self.l1_icache2_freeze_done())
            .field("l1_icache3_freeze_en", &self.l1_icache3_freeze_en())
            .field("l1_icache3_freeze_mode", &self.l1_icache3_freeze_mode())
            .field("l1_icache3_freeze_done", &self.l1_icache3_freeze_done())
            .field("l1_cache_freeze_en", &self.l1_cache_freeze_en())
            .field("l1_cache_freeze_mode", &self.l1_cache_freeze_mode())
            .field("l1_cache_freeze_done", &self.l1_cache_freeze_done())
            .finish()
    }
}
impl W {
    #[doc = "Bit 16 - The bit is used to enable freeze operation on L1-Cache. It can be cleared by software."]
    #[inline(always)]
    pub fn l1_cache_freeze_en(&mut self) -> L1_CACHE_FREEZE_EN_W<'_, L1_CACHE_FREEZE_CTRL_SPEC> {
        L1_CACHE_FREEZE_EN_W::new(self, 16)
    }
    #[doc = "Bit 17 - The bit is used to configure mode of freeze operation L1-Cache. 0: a miss-access will not stuck. 1: a miss-access will stuck."]
    #[inline(always)]
    pub fn l1_cache_freeze_mode(
        &mut self,
    ) -> L1_CACHE_FREEZE_MODE_W<'_, L1_CACHE_FREEZE_CTRL_SPEC> {
        L1_CACHE_FREEZE_MODE_W::new(self, 17)
    }
}
#[doc = "Cache Freeze control register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_freeze_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`l1_cache_freeze_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_FREEZE_CTRL_SPEC;
impl crate::RegisterSpec for L1_CACHE_FREEZE_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_freeze_ctrl::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_FREEZE_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`l1_cache_freeze_ctrl::W`](W) writer structure"]
impl crate::Writable for L1_CACHE_FREEZE_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets L1_CACHE_FREEZE_CTRL to value 0"]
impl crate::Resettable for L1_CACHE_FREEZE_CTRL_SPEC {}
