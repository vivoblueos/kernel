#[doc = "Register `PRIVILEGE_MODE_SEL` reader"]
pub type R = crate::R<PRIVILEGE_MODE_SEL_SPEC>;
#[doc = "Register `PRIVILEGE_MODE_SEL` writer"]
pub type W = crate::W<PRIVILEGE_MODE_SEL_SPEC>;
#[doc = "Field `PRIVILEGE_MODE_SEL` reader - privilege_mode_sel"]
pub type PRIVILEGE_MODE_SEL_R = crate::BitReader;
#[doc = "Field `PRIVILEGE_MODE_SEL` writer - privilege_mode_sel"]
pub type PRIVILEGE_MODE_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - privilege_mode_sel"]
    #[inline(always)]
    pub fn privilege_mode_sel(&self) -> PRIVILEGE_MODE_SEL_R {
        PRIVILEGE_MODE_SEL_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PRIVILEGE_MODE_SEL")
            .field("privilege_mode_sel", &self.privilege_mode_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - privilege_mode_sel"]
    #[inline(always)]
    pub fn privilege_mode_sel(&mut self) -> PRIVILEGE_MODE_SEL_W<'_, PRIVILEGE_MODE_SEL_SPEC> {
        PRIVILEGE_MODE_SEL_W::new(self, 0)
    }
}
#[doc = "SENSITIVE_PRIVILEGE_MODE_SEL_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`privilege_mode_sel::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`privilege_mode_sel::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PRIVILEGE_MODE_SEL_SPEC;
impl crate::RegisterSpec for PRIVILEGE_MODE_SEL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`privilege_mode_sel::R`](R) reader structure"]
impl crate::Readable for PRIVILEGE_MODE_SEL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`privilege_mode_sel::W`](W) writer structure"]
impl crate::Writable for PRIVILEGE_MODE_SEL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PRIVILEGE_MODE_SEL to value 0"]
impl crate::Resettable for PRIVILEGE_MODE_SEL_SPEC {}
