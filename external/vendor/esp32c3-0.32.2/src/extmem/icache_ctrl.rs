#[doc = "Register `ICACHE_CTRL` reader"]
pub type R = crate::R<ICACHE_CTRL_SPEC>;
#[doc = "Register `ICACHE_CTRL` writer"]
pub type W = crate::W<ICACHE_CTRL_SPEC>;
#[doc = "Field `ICACHE_ENABLE` reader - The bit is used to activate the data cache. 0: disable, 1: enable"]
pub type ICACHE_ENABLE_R = crate::BitReader;
#[doc = "Field `ICACHE_ENABLE` writer - The bit is used to activate the data cache. 0: disable, 1: enable"]
pub type ICACHE_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The bit is used to activate the data cache. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn icache_enable(&self) -> ICACHE_ENABLE_R {
        ICACHE_ENABLE_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ICACHE_CTRL")
            .field("icache_enable", &self.icache_enable())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to activate the data cache. 0: disable, 1: enable"]
    #[inline(always)]
    pub fn icache_enable(&mut self) -> ICACHE_ENABLE_W<'_, ICACHE_CTRL_SPEC> {
        ICACHE_ENABLE_W::new(self, 0)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ICACHE_CTRL_SPEC;
impl crate::RegisterSpec for ICACHE_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`icache_ctrl::R`](R) reader structure"]
impl crate::Readable for ICACHE_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`icache_ctrl::W`](W) writer structure"]
impl crate::Writable for ICACHE_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ICACHE_CTRL to value 0"]
impl crate::Resettable for ICACHE_CTRL_SPEC {}
