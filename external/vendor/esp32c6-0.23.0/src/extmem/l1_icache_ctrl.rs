#[doc = "Register `L1_ICACHE_CTRL` reader"]
pub type R = crate::R<L1_ICACHE_CTRL_SPEC>;
#[doc = "Field `L1_ICACHE_SHUT_IBUS0` reader - The bit is used to disable core0 ibus access L1-ICache, 0: enable, 1: disable"]
pub type L1_ICACHE_SHUT_IBUS0_R = crate::BitReader;
#[doc = "Field `L1_ICACHE_SHUT_IBUS1` reader - The bit is used to disable core1 ibus access L1-ICache, 0: enable, 1: disable"]
pub type L1_ICACHE_SHUT_IBUS1_R = crate::BitReader;
#[doc = "Field `L1_ICACHE_SHUT_IBUS2` reader - Reserved"]
pub type L1_ICACHE_SHUT_IBUS2_R = crate::BitReader;
#[doc = "Field `L1_ICACHE_SHUT_IBUS3` reader - Reserved"]
pub type L1_ICACHE_SHUT_IBUS3_R = crate::BitReader;
#[doc = "Field `L1_ICACHE_UNDEF_OP` reader - Reserved"]
pub type L1_ICACHE_UNDEF_OP_R = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - The bit is used to disable core0 ibus access L1-ICache, 0: enable, 1: disable"]
    #[inline(always)]
    pub fn l1_icache_shut_ibus0(&self) -> L1_ICACHE_SHUT_IBUS0_R {
        L1_ICACHE_SHUT_IBUS0_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to disable core1 ibus access L1-ICache, 0: enable, 1: disable"]
    #[inline(always)]
    pub fn l1_icache_shut_ibus1(&self) -> L1_ICACHE_SHUT_IBUS1_R {
        L1_ICACHE_SHUT_IBUS1_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Reserved"]
    #[inline(always)]
    pub fn l1_icache_shut_ibus2(&self) -> L1_ICACHE_SHUT_IBUS2_R {
        L1_ICACHE_SHUT_IBUS2_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Reserved"]
    #[inline(always)]
    pub fn l1_icache_shut_ibus3(&self) -> L1_ICACHE_SHUT_IBUS3_R {
        L1_ICACHE_SHUT_IBUS3_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:7 - Reserved"]
    #[inline(always)]
    pub fn l1_icache_undef_op(&self) -> L1_ICACHE_UNDEF_OP_R {
        L1_ICACHE_UNDEF_OP_R::new(((self.bits >> 4) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_ICACHE_CTRL")
            .field("l1_icache_shut_ibus0", &self.l1_icache_shut_ibus0())
            .field("l1_icache_shut_ibus1", &self.l1_icache_shut_ibus1())
            .field("l1_icache_shut_ibus2", &self.l1_icache_shut_ibus2())
            .field("l1_icache_shut_ibus3", &self.l1_icache_shut_ibus3())
            .field("l1_icache_undef_op", &self.l1_icache_undef_op())
            .finish()
    }
}
#[doc = "L1 instruction Cache(L1-ICache) control register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_icache_ctrl::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_ICACHE_CTRL_SPEC;
impl crate::RegisterSpec for L1_ICACHE_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_icache_ctrl::R`](R) reader structure"]
impl crate::Readable for L1_ICACHE_CTRL_SPEC {}
#[doc = "`reset()` method sets L1_ICACHE_CTRL to value 0"]
impl crate::Resettable for L1_ICACHE_CTRL_SPEC {}
