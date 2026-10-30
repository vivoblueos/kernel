#[doc = "Register `BOD_MODE1_CNTL` reader"]
pub type R = crate::R<BOD_MODE1_CNTL_SPEC>;
#[doc = "Register `BOD_MODE1_CNTL` writer"]
pub type W = crate::W<BOD_MODE1_CNTL_SPEC>;
#[doc = "Field `BOD_MODE1_RESET_ENA` reader - need_des"]
pub type BOD_MODE1_RESET_ENA_R = crate::BitReader;
#[doc = "Field `BOD_MODE1_RESET_ENA` writer - need_des"]
pub type BOD_MODE1_RESET_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn bod_mode1_reset_ena(&self) -> BOD_MODE1_RESET_ENA_R {
        BOD_MODE1_RESET_ENA_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BOD_MODE1_CNTL")
            .field("bod_mode1_reset_ena", &self.bod_mode1_reset_ena())
            .finish()
    }
}
impl W {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn bod_mode1_reset_ena(&mut self) -> BOD_MODE1_RESET_ENA_W<'_, BOD_MODE1_CNTL_SPEC> {
        BOD_MODE1_RESET_ENA_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`bod_mode1_cntl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`bod_mode1_cntl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BOD_MODE1_CNTL_SPEC;
impl crate::RegisterSpec for BOD_MODE1_CNTL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`bod_mode1_cntl::R`](R) reader structure"]
impl crate::Readable for BOD_MODE1_CNTL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`bod_mode1_cntl::W`](W) writer structure"]
impl crate::Writable for BOD_MODE1_CNTL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets BOD_MODE1_CNTL to value 0"]
impl crate::Resettable for BOD_MODE1_CNTL_SPEC {}
