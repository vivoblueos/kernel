#[doc = "Register `WDTCONFIG%s` reader"]
pub type R = crate::R<WDTCONFIG_SPEC>;
#[doc = "Register `WDTCONFIG%s` writer"]
pub type W = crate::W<WDTCONFIG_SPEC>;
#[doc = "Field `HOLD` reader - need_des"]
pub type HOLD_R = crate::FieldReader<u32>;
#[doc = "Field `HOLD` writer - need_des"]
pub type HOLD_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn hold(&self) -> HOLD_R {
        HOLD_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("WDTCONFIG")
            .field("hold", &self.hold())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn hold(&mut self) -> HOLD_W<'_, WDTCONFIG_SPEC> {
        HOLD_W::new(self, 0)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`wdtconfig::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wdtconfig::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct WDTCONFIG_SPEC;
impl crate::RegisterSpec for WDTCONFIG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`wdtconfig::R`](R) reader structure"]
impl crate::Readable for WDTCONFIG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`wdtconfig::W`](W) writer structure"]
impl crate::Writable for WDTCONFIG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets WDTCONFIG%s to value 0x0003_0d40"]
impl crate::Resettable for WDTCONFIG_SPEC {
    const RESET_VALUE: u32 = 0x0003_0d40;
}
