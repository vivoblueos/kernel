#[doc = "Register `FUNC2_1` reader"]
pub type R = crate::R<FUNC2_1_SPEC>;
#[doc = "Register `FUNC2_1` writer"]
pub type W = crate::W<FUNC2_1_SPEC>;
#[doc = "Field `SLC_FUNC2_INT_EN` reader - *******Description***********"]
pub type SLC_FUNC2_INT_EN_R = crate::BitReader;
#[doc = "Field `SLC_FUNC2_INT_EN` writer - *******Description***********"]
pub type SLC_FUNC2_INT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - *******Description***********"]
    #[inline(always)]
    pub fn slc_func2_int_en(&self) -> SLC_FUNC2_INT_EN_R {
        SLC_FUNC2_INT_EN_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FUNC2_1")
            .field("slc_func2_int_en", &self.slc_func2_int_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - *******Description***********"]
    #[inline(always)]
    pub fn slc_func2_int_en(&mut self) -> SLC_FUNC2_INT_EN_W<'_, FUNC2_1_SPEC> {
        SLC_FUNC2_INT_EN_W::new(self, 0)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`func2_1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`func2_1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FUNC2_1_SPEC;
impl crate::RegisterSpec for FUNC2_1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`func2_1::R`](R) reader structure"]
impl crate::Readable for FUNC2_1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`func2_1::W`](W) writer structure"]
impl crate::Writable for FUNC2_1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FUNC2_1 to value 0"]
impl crate::Resettable for FUNC2_1_SPEC {}
