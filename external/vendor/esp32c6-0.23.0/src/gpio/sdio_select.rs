#[doc = "Register `SDIO_SELECT` reader"]
pub type R = crate::R<SDIO_SELECT_SPEC>;
#[doc = "Register `SDIO_SELECT` writer"]
pub type W = crate::W<SDIO_SELECT_SPEC>;
#[doc = "Field `SDIO_SEL` reader - GPIO sdio select register"]
pub type SDIO_SEL_R = crate::FieldReader;
#[doc = "Field `SDIO_SEL` writer - GPIO sdio select register"]
pub type SDIO_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - GPIO sdio select register"]
    #[inline(always)]
    pub fn sdio_sel(&self) -> SDIO_SEL_R {
        SDIO_SEL_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SDIO_SELECT")
            .field("sdio_sel", &self.sdio_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - GPIO sdio select register"]
    #[inline(always)]
    pub fn sdio_sel(&mut self) -> SDIO_SEL_W<'_, SDIO_SELECT_SPEC> {
        SDIO_SEL_W::new(self, 0)
    }
}
#[doc = "GPIO sdio select register\n\nYou can [`read`](crate::Reg::read) this register and get [`sdio_select::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sdio_select::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SDIO_SELECT_SPEC;
impl crate::RegisterSpec for SDIO_SELECT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sdio_select::R`](R) reader structure"]
impl crate::Readable for SDIO_SELECT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sdio_select::W`](W) writer structure"]
impl crate::Writable for SDIO_SELECT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SDIO_SELECT to value 0"]
impl crate::Resettable for SDIO_SELECT_SPEC {}
