#[doc = "Register `L1_CACHE_TAG_MEM_ACS_CONF` reader"]
pub type R = crate::R<L1_CACHE_TAG_MEM_ACS_CONF_SPEC>;
#[doc = "Register `L1_CACHE_TAG_MEM_ACS_CONF` writer"]
pub type W = crate::W<L1_CACHE_TAG_MEM_ACS_CONF_SPEC>;
#[doc = "Field `L1_ICACHE0_TAG_MEM_RD_EN` reader - The bit is used to enable config-bus read L1-ICache0 tag memoryory. 0: disable, 1: enable."]
pub type L1_ICACHE0_TAG_MEM_RD_EN_R = crate::BitReader;
#[doc = "Field `L1_ICACHE0_TAG_MEM_WR_EN` reader - The bit is used to enable config-bus write L1-ICache0 tag memoryory. 0: disable, 1: enable."]
pub type L1_ICACHE0_TAG_MEM_WR_EN_R = crate::BitReader;
#[doc = "Field `L1_ICACHE1_TAG_MEM_RD_EN` reader - The bit is used to enable config-bus read L1-ICache1 tag memoryory. 0: disable, 1: enable."]
pub type L1_ICACHE1_TAG_MEM_RD_EN_R = crate::BitReader;
#[doc = "Field `L1_ICACHE1_TAG_MEM_WR_EN` reader - The bit is used to enable config-bus write L1-ICache1 tag memoryory. 0: disable, 1: enable."]
pub type L1_ICACHE1_TAG_MEM_WR_EN_R = crate::BitReader;
#[doc = "Field `L1_ICACHE2_TAG_MEM_RD_EN` reader - Reserved"]
pub type L1_ICACHE2_TAG_MEM_RD_EN_R = crate::BitReader;
#[doc = "Field `L1_ICACHE2_TAG_MEM_WR_EN` reader - Reserved"]
pub type L1_ICACHE2_TAG_MEM_WR_EN_R = crate::BitReader;
#[doc = "Field `L1_ICACHE3_TAG_MEM_RD_EN` reader - Reserved"]
pub type L1_ICACHE3_TAG_MEM_RD_EN_R = crate::BitReader;
#[doc = "Field `L1_ICACHE3_TAG_MEM_WR_EN` reader - Reserved"]
pub type L1_ICACHE3_TAG_MEM_WR_EN_R = crate::BitReader;
#[doc = "Field `L1_CACHE_TAG_MEM_RD_EN` reader - The bit is used to enable config-bus read L1-Cache tag memoryory. 0: disable, 1: enable."]
pub type L1_CACHE_TAG_MEM_RD_EN_R = crate::BitReader;
#[doc = "Field `L1_CACHE_TAG_MEM_RD_EN` writer - The bit is used to enable config-bus read L1-Cache tag memoryory. 0: disable, 1: enable."]
pub type L1_CACHE_TAG_MEM_RD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_CACHE_TAG_MEM_WR_EN` reader - The bit is used to enable config-bus write L1-Cache tag memoryory. 0: disable, 1: enable."]
pub type L1_CACHE_TAG_MEM_WR_EN_R = crate::BitReader;
#[doc = "Field `L1_CACHE_TAG_MEM_WR_EN` writer - The bit is used to enable config-bus write L1-Cache tag memoryory. 0: disable, 1: enable."]
pub type L1_CACHE_TAG_MEM_WR_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The bit is used to enable config-bus read L1-ICache0 tag memoryory. 0: disable, 1: enable."]
    #[inline(always)]
    pub fn l1_icache0_tag_mem_rd_en(&self) -> L1_ICACHE0_TAG_MEM_RD_EN_R {
        L1_ICACHE0_TAG_MEM_RD_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to enable config-bus write L1-ICache0 tag memoryory. 0: disable, 1: enable."]
    #[inline(always)]
    pub fn l1_icache0_tag_mem_wr_en(&self) -> L1_ICACHE0_TAG_MEM_WR_EN_R {
        L1_ICACHE0_TAG_MEM_WR_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 4 - The bit is used to enable config-bus read L1-ICache1 tag memoryory. 0: disable, 1: enable."]
    #[inline(always)]
    pub fn l1_icache1_tag_mem_rd_en(&self) -> L1_ICACHE1_TAG_MEM_RD_EN_R {
        L1_ICACHE1_TAG_MEM_RD_EN_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The bit is used to enable config-bus write L1-ICache1 tag memoryory. 0: disable, 1: enable."]
    #[inline(always)]
    pub fn l1_icache1_tag_mem_wr_en(&self) -> L1_ICACHE1_TAG_MEM_WR_EN_R {
        L1_ICACHE1_TAG_MEM_WR_EN_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 8 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_tag_mem_rd_en(&self) -> L1_ICACHE2_TAG_MEM_RD_EN_R {
        L1_ICACHE2_TAG_MEM_RD_EN_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_tag_mem_wr_en(&self) -> L1_ICACHE2_TAG_MEM_WR_EN_R {
        L1_ICACHE2_TAG_MEM_WR_EN_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 12 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_tag_mem_rd_en(&self) -> L1_ICACHE3_TAG_MEM_RD_EN_R {
        L1_ICACHE3_TAG_MEM_RD_EN_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_tag_mem_wr_en(&self) -> L1_ICACHE3_TAG_MEM_WR_EN_R {
        L1_ICACHE3_TAG_MEM_WR_EN_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 16 - The bit is used to enable config-bus read L1-Cache tag memoryory. 0: disable, 1: enable."]
    #[inline(always)]
    pub fn l1_cache_tag_mem_rd_en(&self) -> L1_CACHE_TAG_MEM_RD_EN_R {
        L1_CACHE_TAG_MEM_RD_EN_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - The bit is used to enable config-bus write L1-Cache tag memoryory. 0: disable, 1: enable."]
    #[inline(always)]
    pub fn l1_cache_tag_mem_wr_en(&self) -> L1_CACHE_TAG_MEM_WR_EN_R {
        L1_CACHE_TAG_MEM_WR_EN_R::new(((self.bits >> 17) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_TAG_MEM_ACS_CONF")
            .field("l1_icache0_tag_mem_rd_en", &self.l1_icache0_tag_mem_rd_en())
            .field("l1_icache0_tag_mem_wr_en", &self.l1_icache0_tag_mem_wr_en())
            .field("l1_icache1_tag_mem_rd_en", &self.l1_icache1_tag_mem_rd_en())
            .field("l1_icache1_tag_mem_wr_en", &self.l1_icache1_tag_mem_wr_en())
            .field("l1_icache2_tag_mem_rd_en", &self.l1_icache2_tag_mem_rd_en())
            .field("l1_icache2_tag_mem_wr_en", &self.l1_icache2_tag_mem_wr_en())
            .field("l1_icache3_tag_mem_rd_en", &self.l1_icache3_tag_mem_rd_en())
            .field("l1_icache3_tag_mem_wr_en", &self.l1_icache3_tag_mem_wr_en())
            .field("l1_cache_tag_mem_rd_en", &self.l1_cache_tag_mem_rd_en())
            .field("l1_cache_tag_mem_wr_en", &self.l1_cache_tag_mem_wr_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 16 - The bit is used to enable config-bus read L1-Cache tag memoryory. 0: disable, 1: enable."]
    #[inline(always)]
    pub fn l1_cache_tag_mem_rd_en(
        &mut self,
    ) -> L1_CACHE_TAG_MEM_RD_EN_W<'_, L1_CACHE_TAG_MEM_ACS_CONF_SPEC> {
        L1_CACHE_TAG_MEM_RD_EN_W::new(self, 16)
    }
    #[doc = "Bit 17 - The bit is used to enable config-bus write L1-Cache tag memoryory. 0: disable, 1: enable."]
    #[inline(always)]
    pub fn l1_cache_tag_mem_wr_en(
        &mut self,
    ) -> L1_CACHE_TAG_MEM_WR_EN_W<'_, L1_CACHE_TAG_MEM_ACS_CONF_SPEC> {
        L1_CACHE_TAG_MEM_WR_EN_W::new(self, 17)
    }
}
#[doc = "Cache tag memory access configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_tag_mem_acs_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`l1_cache_tag_mem_acs_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_TAG_MEM_ACS_CONF_SPEC;
impl crate::RegisterSpec for L1_CACHE_TAG_MEM_ACS_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_tag_mem_acs_conf::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_TAG_MEM_ACS_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`l1_cache_tag_mem_acs_conf::W`](W) writer structure"]
impl crate::Writable for L1_CACHE_TAG_MEM_ACS_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets L1_CACHE_TAG_MEM_ACS_CONF to value 0x0003_3333"]
impl crate::Resettable for L1_CACHE_TAG_MEM_ACS_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0003_3333;
}
