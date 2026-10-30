#[doc = "Register `CONFIG_UPDATE` writer"]
pub type W = crate::W<CONFIG_UPDATE_SPEC>;
#[doc = "Field `CONFIG_UPDATE` writer - Write 1 to this register would update the value of configure registers from APB clock domain to 48MHz clock domain."]
pub type CONFIG_UPDATE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<CONFIG_UPDATE_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Write 1 to this register would update the value of configure registers from APB clock domain to 48MHz clock domain."]
    #[inline(always)]
    pub fn config_update(&mut self) -> CONFIG_UPDATE_W<'_, CONFIG_UPDATE_SPEC> {
        CONFIG_UPDATE_W::new(self, 0)
    }
}
#[doc = "Configuration registers' value update\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`config_update::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONFIG_UPDATE_SPEC;
impl crate::RegisterSpec for CONFIG_UPDATE_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`config_update::W`](W) writer structure"]
impl crate::Writable for CONFIG_UPDATE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONFIG_UPDATE to value 0"]
impl crate::Resettable for CONFIG_UPDATE_SPEC {}
