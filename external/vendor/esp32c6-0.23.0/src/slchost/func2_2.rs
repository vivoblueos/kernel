#[doc = "Register `FUNC2_2` reader"]
pub type R = crate::R<FUNC2_2_SPEC>;
#[doc = "Register `FUNC2_2` writer"]
pub type W = crate::W<FUNC2_2_SPEC>;
#[doc = "Field `SLC_FUNC1_MDSTAT` reader - *******Description***********"]
pub type SLC_FUNC1_MDSTAT_R = crate::BitReader;
#[doc = "Field `SLC_FUNC1_MDSTAT` writer - *******Description***********"]
pub type SLC_FUNC1_MDSTAT_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - *******Description***********"]
    #[inline(always)]
    pub fn slc_func1_mdstat(&self) -> SLC_FUNC1_MDSTAT_R {
        SLC_FUNC1_MDSTAT_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("FUNC2_2")
            .field("slc_func1_mdstat", &self.slc_func1_mdstat())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - *******Description***********"]
    #[inline(always)]
    pub fn slc_func1_mdstat(&mut self) -> SLC_FUNC1_MDSTAT_W<'_, FUNC2_2_SPEC> {
        SLC_FUNC1_MDSTAT_W::new(self, 0)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`func2_2::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`func2_2::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FUNC2_2_SPEC;
impl crate::RegisterSpec for FUNC2_2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`func2_2::R`](R) reader structure"]
impl crate::Readable for FUNC2_2_SPEC {}
#[doc = "`write(|w| ..)` method takes [`func2_2::W`](W) writer structure"]
impl crate::Writable for FUNC2_2_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets FUNC2_2 to value 0x01"]
impl crate::Resettable for FUNC2_2_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
