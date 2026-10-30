#[doc = "Register `CFG_UPDATE` writer"]
pub type W = crate::W<CFG_UPDATE_SPEC>;
#[doc = "Field `CONF_UPDATE` writer - update the timing configurations"]
pub type CONF_UPDATE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<CFG_UPDATE_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - update the timing configurations"]
    #[inline(always)]
    pub fn conf_update(&mut self) -> CONF_UPDATE_W<'_, CFG_UPDATE_SPEC> {
        CONF_UPDATE_W::new(self, 0)
    }
}
#[doc = "update sdio configurations\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cfg_update::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CFG_UPDATE_SPEC;
impl crate::RegisterSpec for CFG_UPDATE_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`cfg_update::W`](W) writer structure"]
impl crate::Writable for CFG_UPDATE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CFG_UPDATE to value 0"]
impl crate::Resettable for CFG_UPDATE_SPEC {}
