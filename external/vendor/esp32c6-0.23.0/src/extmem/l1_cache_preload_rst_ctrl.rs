#[doc = "Register `L1_CACHE_PRELOAD_RST_CTRL` reader"]
pub type R = crate::R<L1_CACHE_PRELOAD_RST_CTRL_SPEC>;
#[doc = "Register `L1_CACHE_PRELOAD_RST_CTRL` writer"]
pub type W = crate::W<L1_CACHE_PRELOAD_RST_CTRL_SPEC>;
#[doc = "Field `L1_ICACHE0_PLD_RST` reader - set this bit to reset preload-logic inside L1-ICache0. Recommend that this should only be used to initialize preload-logic when some fatal error of preload-logic occurs."]
pub type L1_ICACHE0_PLD_RST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE1_PLD_RST` reader - set this bit to reset preload-logic inside L1-ICache1. Recommend that this should only be used to initialize preload-logic when some fatal error of preload-logic occurs."]
pub type L1_ICACHE1_PLD_RST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE2_PLD_RST` reader - Reserved"]
pub type L1_ICACHE2_PLD_RST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE3_PLD_RST` reader - Reserved"]
pub type L1_ICACHE3_PLD_RST_R = crate::BitReader;
#[doc = "Field `L1_CACHE_PLD_RST` reader - set this bit to reset preload-logic inside L1-Cache. Recommend that this should only be used to initialize preload-logic when some fatal error of preload-logic occurs."]
pub type L1_CACHE_PLD_RST_R = crate::BitReader;
#[doc = "Field `L1_CACHE_PLD_RST` writer - set this bit to reset preload-logic inside L1-Cache. Recommend that this should only be used to initialize preload-logic when some fatal error of preload-logic occurs."]
pub type L1_CACHE_PLD_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - set this bit to reset preload-logic inside L1-ICache0. Recommend that this should only be used to initialize preload-logic when some fatal error of preload-logic occurs."]
    #[inline(always)]
    pub fn l1_icache0_pld_rst(&self) -> L1_ICACHE0_PLD_RST_R {
        L1_ICACHE0_PLD_RST_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - set this bit to reset preload-logic inside L1-ICache1. Recommend that this should only be used to initialize preload-logic when some fatal error of preload-logic occurs."]
    #[inline(always)]
    pub fn l1_icache1_pld_rst(&self) -> L1_ICACHE1_PLD_RST_R {
        L1_ICACHE1_PLD_RST_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_pld_rst(&self) -> L1_ICACHE2_PLD_RST_R {
        L1_ICACHE2_PLD_RST_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_pld_rst(&self) -> L1_ICACHE3_PLD_RST_R {
        L1_ICACHE3_PLD_RST_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - set this bit to reset preload-logic inside L1-Cache. Recommend that this should only be used to initialize preload-logic when some fatal error of preload-logic occurs."]
    #[inline(always)]
    pub fn l1_cache_pld_rst(&self) -> L1_CACHE_PLD_RST_R {
        L1_CACHE_PLD_RST_R::new(((self.bits >> 4) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_PRELOAD_RST_CTRL")
            .field("l1_icache0_pld_rst", &self.l1_icache0_pld_rst())
            .field("l1_icache1_pld_rst", &self.l1_icache1_pld_rst())
            .field("l1_icache2_pld_rst", &self.l1_icache2_pld_rst())
            .field("l1_icache3_pld_rst", &self.l1_icache3_pld_rst())
            .field("l1_cache_pld_rst", &self.l1_cache_pld_rst())
            .finish()
    }
}
impl W {
    #[doc = "Bit 4 - set this bit to reset preload-logic inside L1-Cache. Recommend that this should only be used to initialize preload-logic when some fatal error of preload-logic occurs."]
    #[inline(always)]
    pub fn l1_cache_pld_rst(&mut self) -> L1_CACHE_PLD_RST_W<'_, L1_CACHE_PRELOAD_RST_CTRL_SPEC> {
        L1_CACHE_PLD_RST_W::new(self, 4)
    }
}
#[doc = "Cache Preload Reset control register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_preload_rst_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`l1_cache_preload_rst_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_PRELOAD_RST_CTRL_SPEC;
impl crate::RegisterSpec for L1_CACHE_PRELOAD_RST_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_preload_rst_ctrl::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_PRELOAD_RST_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`l1_cache_preload_rst_ctrl::W`](W) writer structure"]
impl crate::Writable for L1_CACHE_PRELOAD_RST_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets L1_CACHE_PRELOAD_RST_CTRL to value 0"]
impl crate::Resettable for L1_CACHE_PRELOAD_RST_CTRL_SPEC {}
