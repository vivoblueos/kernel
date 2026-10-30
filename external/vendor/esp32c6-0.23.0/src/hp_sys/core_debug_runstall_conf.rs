#[doc = "Register `CORE_DEBUG_RUNSTALL_CONF` reader"]
pub type R = crate::R<CORE_DEBUG_RUNSTALL_CONF_SPEC>;
#[doc = "Register `CORE_DEBUG_RUNSTALL_CONF` writer"]
pub type W = crate::W<CORE_DEBUG_RUNSTALL_CONF_SPEC>;
#[doc = "Field `CORE_DEBUG_RUNSTALL_ENABLE` reader - Set this field to 1 to enable debug runstall feature between HP-core and LP-core."]
pub type CORE_DEBUG_RUNSTALL_ENABLE_R = crate::BitReader;
#[doc = "Field `CORE_DEBUG_RUNSTALL_ENABLE` writer - Set this field to 1 to enable debug runstall feature between HP-core and LP-core."]
pub type CORE_DEBUG_RUNSTALL_ENABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set this field to 1 to enable debug runstall feature between HP-core and LP-core."]
    #[inline(always)]
    pub fn core_debug_runstall_enable(&self) -> CORE_DEBUG_RUNSTALL_ENABLE_R {
        CORE_DEBUG_RUNSTALL_ENABLE_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE_DEBUG_RUNSTALL_CONF")
            .field(
                "core_debug_runstall_enable",
                &self.core_debug_runstall_enable(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set this field to 1 to enable debug runstall feature between HP-core and LP-core."]
    #[inline(always)]
    pub fn core_debug_runstall_enable(
        &mut self,
    ) -> CORE_DEBUG_RUNSTALL_ENABLE_W<'_, CORE_DEBUG_RUNSTALL_CONF_SPEC> {
        CORE_DEBUG_RUNSTALL_ENABLE_W::new(self, 0)
    }
}
#[doc = "Core Debug runstall configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`core_debug_runstall_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_debug_runstall_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE_DEBUG_RUNSTALL_CONF_SPEC;
impl crate::RegisterSpec for CORE_DEBUG_RUNSTALL_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core_debug_runstall_conf::R`](R) reader structure"]
impl crate::Readable for CORE_DEBUG_RUNSTALL_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`core_debug_runstall_conf::W`](W) writer structure"]
impl crate::Writable for CORE_DEBUG_RUNSTALL_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CORE_DEBUG_RUNSTALL_CONF to value 0"]
impl crate::Resettable for CORE_DEBUG_RUNSTALL_CONF_SPEC {}
