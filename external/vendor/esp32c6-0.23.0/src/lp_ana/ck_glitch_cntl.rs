#[doc = "Register `CK_GLITCH_CNTL` reader"]
pub type R = crate::R<CK_GLITCH_CNTL_SPEC>;
#[doc = "Register `CK_GLITCH_CNTL` writer"]
pub type W = crate::W<CK_GLITCH_CNTL_SPEC>;
#[doc = "Field `CK_GLITCH_RESET_ENA` reader - need_des"]
pub type CK_GLITCH_RESET_ENA_R = crate::BitReader;
#[doc = "Field `CK_GLITCH_RESET_ENA` writer - need_des"]
pub type CK_GLITCH_RESET_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn ck_glitch_reset_ena(&self) -> CK_GLITCH_RESET_ENA_R {
        CK_GLITCH_RESET_ENA_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CK_GLITCH_CNTL")
            .field("ck_glitch_reset_ena", &self.ck_glitch_reset_ena())
            .finish()
    }
}
impl W {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn ck_glitch_reset_ena(&mut self) -> CK_GLITCH_RESET_ENA_W<'_, CK_GLITCH_CNTL_SPEC> {
        CK_GLITCH_RESET_ENA_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`ck_glitch_cntl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ck_glitch_cntl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CK_GLITCH_CNTL_SPEC;
impl crate::RegisterSpec for CK_GLITCH_CNTL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ck_glitch_cntl::R`](R) reader structure"]
impl crate::Readable for CK_GLITCH_CNTL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ck_glitch_cntl::W`](W) writer structure"]
impl crate::Writable for CK_GLITCH_CNTL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CK_GLITCH_CNTL to value 0"]
impl crate::Resettable for CK_GLITCH_CNTL_SPEC {}
