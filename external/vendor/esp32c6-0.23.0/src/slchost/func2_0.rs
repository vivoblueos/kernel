#[doc = "Register `FUNC2_0` reader"]
pub type R = crate::R<FUNC2_0_SPEC>;
#[doc = "Register `FUNC2_0` writer"]
pub type W = crate::W<FUNC2_0_SPEC>;
#[doc = "Field `SLC_FUNC2_INT` reader - *******Description***********"]
pub type SLC_FUNC2_INT_R = crate::BitReader;
#[doc = "Field `SLC_FUNC2_INT` writer - *******Description***********"]
pub type SLC_FUNC2_INT_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 24 - *******Description***********"]
    #[inline(always)]
    pub fn slc_func2_int(&self) -> SLC_FUNC2_INT_R {
        SLC_FUNC2_INT_R::new(((self.bits >> 24) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FUNC2_0")
            .field("slc_func2_int", &self.slc_func2_int())
            .finish()
    }
}
impl W {
    #[doc = "Bit 24 - *******Description***********"]
    #[inline(always)]
    pub fn slc_func2_int(&mut self) -> SLC_FUNC2_INT_W<'_, FUNC2_0_SPEC> {
        SLC_FUNC2_INT_W::new(self, 24)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`func2_0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`func2_0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FUNC2_0_SPEC;
impl crate::RegisterSpec for FUNC2_0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`func2_0::R`](R) reader structure"]
impl crate::Readable for FUNC2_0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`func2_0::W`](W) writer structure"]
impl crate::Writable for FUNC2_0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FUNC2_0 to value 0"]
impl crate::Resettable for FUNC2_0_SPEC {}
