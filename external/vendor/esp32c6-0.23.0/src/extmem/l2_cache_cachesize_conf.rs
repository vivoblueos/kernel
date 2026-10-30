#[doc = "Register `L2_CACHE_CACHESIZE_CONF` reader"]
pub type R = crate::R<L2_CACHE_CACHESIZE_CONF_SPEC>;
#[doc = "Field `L2_CACHE_CACHESIZE_1K` reader - The field is used to configure cachesize of L2-Cache as 1k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_1K_R = crate::BitReader;
#[doc = "Field `L2_CACHE_CACHESIZE_2K` reader - The field is used to configure cachesize of L2-Cache as 2k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_2K_R = crate::BitReader;
#[doc = "Field `L2_CACHE_CACHESIZE_4K` reader - The field is used to configure cachesize of L2-Cache as 4k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_4K_R = crate::BitReader;
#[doc = "Field `L2_CACHE_CACHESIZE_8K` reader - The field is used to configure cachesize of L2-Cache as 8k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_8K_R = crate::BitReader;
#[doc = "Field `L2_CACHE_CACHESIZE_16K` reader - The field is used to configure cachesize of L2-Cache as 16k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_16K_R = crate::BitReader;
#[doc = "Field `L2_CACHE_CACHESIZE_32K` reader - The field is used to configure cachesize of L2-Cache as 32k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_32K_R = crate::BitReader;
#[doc = "Field `L2_CACHE_CACHESIZE_64K` reader - The field is used to configure cachesize of L2-Cache as 64k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_64K_R = crate::BitReader;
#[doc = "Field `L2_CACHE_CACHESIZE_128K` reader - The field is used to configure cachesize of L2-Cache as 128k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_128K_R = crate::BitReader;
#[doc = "Field `L2_CACHE_CACHESIZE_256K` reader - The field is used to configure cachesize of L2-Cache as 256k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_256K_R = crate::BitReader;
#[doc = "Field `L2_CACHE_CACHESIZE_512K` reader - The field is used to configure cachesize of L2-Cache as 512k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_512K_R = crate::BitReader;
#[doc = "Field `L2_CACHE_CACHESIZE_1024K` reader - The field is used to configure cachesize of L2-Cache as 1024k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_1024K_R = crate::BitReader;
#[doc = "Field `L2_CACHE_CACHESIZE_2048K` reader - The field is used to configure cachesize of L2-Cache as 2048k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_2048K_R = crate::BitReader;
#[doc = "Field `L2_CACHE_CACHESIZE_4096K` reader - The field is used to configure cachesize of L2-Cache as 4096k bytes. This field and all other fields within this register is onehot."]
pub type L2_CACHE_CACHESIZE_4096K_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The field is used to configure cachesize of L2-Cache as 1k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_1k(&self) -> L2_CACHE_CACHESIZE_1K_R {
        L2_CACHE_CACHESIZE_1K_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The field is used to configure cachesize of L2-Cache as 2k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_2k(&self) -> L2_CACHE_CACHESIZE_2K_R {
        L2_CACHE_CACHESIZE_2K_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The field is used to configure cachesize of L2-Cache as 4k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_4k(&self) -> L2_CACHE_CACHESIZE_4K_R {
        L2_CACHE_CACHESIZE_4K_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The field is used to configure cachesize of L2-Cache as 8k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_8k(&self) -> L2_CACHE_CACHESIZE_8K_R {
        L2_CACHE_CACHESIZE_8K_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The field is used to configure cachesize of L2-Cache as 16k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_16k(&self) -> L2_CACHE_CACHESIZE_16K_R {
        L2_CACHE_CACHESIZE_16K_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The field is used to configure cachesize of L2-Cache as 32k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_32k(&self) -> L2_CACHE_CACHESIZE_32K_R {
        L2_CACHE_CACHESIZE_32K_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The field is used to configure cachesize of L2-Cache as 64k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_64k(&self) -> L2_CACHE_CACHESIZE_64K_R {
        L2_CACHE_CACHESIZE_64K_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The field is used to configure cachesize of L2-Cache as 128k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_128k(&self) -> L2_CACHE_CACHESIZE_128K_R {
        L2_CACHE_CACHESIZE_128K_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The field is used to configure cachesize of L2-Cache as 256k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_256k(&self) -> L2_CACHE_CACHESIZE_256K_R {
        L2_CACHE_CACHESIZE_256K_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The field is used to configure cachesize of L2-Cache as 512k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_512k(&self) -> L2_CACHE_CACHESIZE_512K_R {
        L2_CACHE_CACHESIZE_512K_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - The field is used to configure cachesize of L2-Cache as 1024k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_1024k(&self) -> L2_CACHE_CACHESIZE_1024K_R {
        L2_CACHE_CACHESIZE_1024K_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - The field is used to configure cachesize of L2-Cache as 2048k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_2048k(&self) -> L2_CACHE_CACHESIZE_2048K_R {
        L2_CACHE_CACHESIZE_2048K_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - The field is used to configure cachesize of L2-Cache as 4096k bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l2_cache_cachesize_4096k(&self) -> L2_CACHE_CACHESIZE_4096K_R {
        L2_CACHE_CACHESIZE_4096K_R::new(((self.bits >> 12) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L2_CACHE_CACHESIZE_CONF")
            .field("l2_cache_cachesize_1k", &self.l2_cache_cachesize_1k())
            .field("l2_cache_cachesize_2k", &self.l2_cache_cachesize_2k())
            .field("l2_cache_cachesize_4k", &self.l2_cache_cachesize_4k())
            .field("l2_cache_cachesize_8k", &self.l2_cache_cachesize_8k())
            .field("l2_cache_cachesize_16k", &self.l2_cache_cachesize_16k())
            .field("l2_cache_cachesize_32k", &self.l2_cache_cachesize_32k())
            .field("l2_cache_cachesize_64k", &self.l2_cache_cachesize_64k())
            .field("l2_cache_cachesize_128k", &self.l2_cache_cachesize_128k())
            .field("l2_cache_cachesize_256k", &self.l2_cache_cachesize_256k())
            .field("l2_cache_cachesize_512k", &self.l2_cache_cachesize_512k())
            .field("l2_cache_cachesize_1024k", &self.l2_cache_cachesize_1024k())
            .field("l2_cache_cachesize_2048k", &self.l2_cache_cachesize_2048k())
            .field("l2_cache_cachesize_4096k", &self.l2_cache_cachesize_4096k())
            .finish()
    }
}
#[doc = "L2 Cache CacheSize mode configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l2_cache_cachesize_conf::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L2_CACHE_CACHESIZE_CONF_SPEC;
impl crate::RegisterSpec for L2_CACHE_CACHESIZE_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l2_cache_cachesize_conf::R`](R) reader structure"]
impl crate::Readable for L2_CACHE_CACHESIZE_CONF_SPEC {}
#[doc = "`reset()` method sets L2_CACHE_CACHESIZE_CONF to value 0"]
impl crate::Resettable for L2_CACHE_CACHESIZE_CONF_SPEC {}
