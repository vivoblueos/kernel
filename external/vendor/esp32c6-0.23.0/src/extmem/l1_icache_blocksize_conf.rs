#[doc = "Register `L1_ICACHE_BLOCKSIZE_CONF` reader"]
pub type R = crate::R<L1_ICACHE_BLOCKSIZE_CONF_SPEC>;
#[doc = "Field `L1_ICACHE_BLOCKSIZE_8` reader - The field is used to configureblocksize of L1-ICache as 8 bytes. This field and all other fields within this register is onehot."]
pub type L1_ICACHE_BLOCKSIZE_8_R = crate::BitReader;
#[doc = "Field `L1_ICACHE_BLOCKSIZE_16` reader - The field is used to configureblocksize of L1-ICache as 16 bytes. This field and all other fields within this register is onehot."]
pub type L1_ICACHE_BLOCKSIZE_16_R = crate::BitReader;
#[doc = "Field `L1_ICACHE_BLOCKSIZE_32` reader - The field is used to configureblocksize of L1-ICache as 32 bytes. This field and all other fields within this register is onehot."]
pub type L1_ICACHE_BLOCKSIZE_32_R = crate::BitReader;
#[doc = "Field `L1_ICACHE_BLOCKSIZE_64` reader - The field is used to configureblocksize of L1-ICache as 64 bytes. This field and all other fields within this register is onehot."]
pub type L1_ICACHE_BLOCKSIZE_64_R = crate::BitReader;
#[doc = "Field `L1_ICACHE_BLOCKSIZE_128` reader - The field is used to configureblocksize of L1-ICache as 128 bytes. This field and all other fields within this register is onehot."]
pub type L1_ICACHE_BLOCKSIZE_128_R = crate::BitReader;
#[doc = "Field `L1_ICACHE_BLOCKSIZE_256` reader - The field is used to configureblocksize of L1-ICache as 256 bytes. This field and all other fields within this register is onehot."]
pub type L1_ICACHE_BLOCKSIZE_256_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The field is used to configureblocksize of L1-ICache as 8 bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l1_icache_blocksize_8(&self) -> L1_ICACHE_BLOCKSIZE_8_R {
        L1_ICACHE_BLOCKSIZE_8_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The field is used to configureblocksize of L1-ICache as 16 bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l1_icache_blocksize_16(&self) -> L1_ICACHE_BLOCKSIZE_16_R {
        L1_ICACHE_BLOCKSIZE_16_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The field is used to configureblocksize of L1-ICache as 32 bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l1_icache_blocksize_32(&self) -> L1_ICACHE_BLOCKSIZE_32_R {
        L1_ICACHE_BLOCKSIZE_32_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The field is used to configureblocksize of L1-ICache as 64 bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l1_icache_blocksize_64(&self) -> L1_ICACHE_BLOCKSIZE_64_R {
        L1_ICACHE_BLOCKSIZE_64_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The field is used to configureblocksize of L1-ICache as 128 bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l1_icache_blocksize_128(&self) -> L1_ICACHE_BLOCKSIZE_128_R {
        L1_ICACHE_BLOCKSIZE_128_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The field is used to configureblocksize of L1-ICache as 256 bytes. This field and all other fields within this register is onehot."]
    #[inline(always)]
    pub fn l1_icache_blocksize_256(&self) -> L1_ICACHE_BLOCKSIZE_256_R {
        L1_ICACHE_BLOCKSIZE_256_R::new(((self.bits >> 5) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_ICACHE_BLOCKSIZE_CONF")
            .field("l1_icache_blocksize_8", &self.l1_icache_blocksize_8())
            .field("l1_icache_blocksize_16", &self.l1_icache_blocksize_16())
            .field("l1_icache_blocksize_32", &self.l1_icache_blocksize_32())
            .field("l1_icache_blocksize_64", &self.l1_icache_blocksize_64())
            .field("l1_icache_blocksize_128", &self.l1_icache_blocksize_128())
            .field("l1_icache_blocksize_256", &self.l1_icache_blocksize_256())
            .finish()
    }
}
#[doc = "L1 instruction Cache BlockSize mode configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_icache_blocksize_conf::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_ICACHE_BLOCKSIZE_CONF_SPEC;
impl crate::RegisterSpec for L1_ICACHE_BLOCKSIZE_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_icache_blocksize_conf::R`](R) reader structure"]
impl crate::Readable for L1_ICACHE_BLOCKSIZE_CONF_SPEC {}
#[doc = "`reset()` method sets L1_ICACHE_BLOCKSIZE_CONF to value 0"]
impl crate::Resettable for L1_ICACHE_BLOCKSIZE_CONF_SPEC {}
