#[doc = "Register `L1_CACHE_PRELOCK_CONF` reader"]
pub type R = crate::R<L1_CACHE_PRELOCK_CONF_SPEC>;
#[doc = "Register `L1_CACHE_PRELOCK_CONF` writer"]
pub type W = crate::W<L1_CACHE_PRELOCK_CONF_SPEC>;
#[doc = "Field `L1_CACHE_PRELOCK_SCT0_EN` reader - The bit is used to enable the first section of prelock function on L1-Cache."]
pub type L1_CACHE_PRELOCK_SCT0_EN_R = crate::BitReader;
#[doc = "Field `L1_CACHE_PRELOCK_SCT0_EN` writer - The bit is used to enable the first section of prelock function on L1-Cache."]
pub type L1_CACHE_PRELOCK_SCT0_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_CACHE_PRELOCK_SCT1_EN` reader - The bit is used to enable the second section of prelock function on L1-Cache."]
pub type L1_CACHE_PRELOCK_SCT1_EN_R = crate::BitReader;
#[doc = "Field `L1_CACHE_PRELOCK_SCT1_EN` writer - The bit is used to enable the second section of prelock function on L1-Cache."]
pub type L1_CACHE_PRELOCK_SCT1_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_CACHE_PRELOCK_RGID` reader - The bit is used to set the gid of l1 cache prelock."]
pub type L1_CACHE_PRELOCK_RGID_R = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - The bit is used to enable the first section of prelock function on L1-Cache."]
    #[inline(always)]
    pub fn l1_cache_prelock_sct0_en(&self) -> L1_CACHE_PRELOCK_SCT0_EN_R {
        L1_CACHE_PRELOCK_SCT0_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to enable the second section of prelock function on L1-Cache."]
    #[inline(always)]
    pub fn l1_cache_prelock_sct1_en(&self) -> L1_CACHE_PRELOCK_SCT1_EN_R {
        L1_CACHE_PRELOCK_SCT1_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:5 - The bit is used to set the gid of l1 cache prelock."]
    #[inline(always)]
    pub fn l1_cache_prelock_rgid(&self) -> L1_CACHE_PRELOCK_RGID_R {
        L1_CACHE_PRELOCK_RGID_R::new(((self.bits >> 2) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_PRELOCK_CONF")
            .field("l1_cache_prelock_sct0_en", &self.l1_cache_prelock_sct0_en())
            .field("l1_cache_prelock_sct1_en", &self.l1_cache_prelock_sct1_en())
            .field("l1_cache_prelock_rgid", &self.l1_cache_prelock_rgid())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to enable the first section of prelock function on L1-Cache."]
    #[inline(always)]
    pub fn l1_cache_prelock_sct0_en(
        &mut self,
    ) -> L1_CACHE_PRELOCK_SCT0_EN_W<'_, L1_CACHE_PRELOCK_CONF_SPEC> {
        L1_CACHE_PRELOCK_SCT0_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - The bit is used to enable the second section of prelock function on L1-Cache."]
    #[inline(always)]
    pub fn l1_cache_prelock_sct1_en(
        &mut self,
    ) -> L1_CACHE_PRELOCK_SCT1_EN_W<'_, L1_CACHE_PRELOCK_CONF_SPEC> {
        L1_CACHE_PRELOCK_SCT1_EN_W::new(self, 1)
    }
}
#[doc = "L1 Cache prelock configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_prelock_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`l1_cache_prelock_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_PRELOCK_CONF_SPEC;
impl crate::RegisterSpec for L1_CACHE_PRELOCK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_prelock_conf::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_PRELOCK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`l1_cache_prelock_conf::W`](W) writer structure"]
impl crate::Writable for L1_CACHE_PRELOCK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets L1_CACHE_PRELOCK_CONF to value 0"]
impl crate::Resettable for L1_CACHE_PRELOCK_CONF_SPEC {}
