#[doc = "Register `PGM_DATA7` reader"]
pub type R = crate::R<PGM_DATA7_SPEC>;
#[doc = "Register `PGM_DATA7` writer"]
pub type W = crate::W<PGM_DATA7_SPEC>;
#[doc = "Field `PGM_DATA_7` reader - Configures the 7th 32-bit data to be programmed."]
pub type PGM_DATA_7_R = crate::FieldReader<u32>;
#[doc = "Field `PGM_DATA_7` writer - Configures the 7th 32-bit data to be programmed."]
pub type PGM_DATA_7_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Configures the 7th 32-bit data to be programmed."]
    #[inline(always)]
    pub fn pgm_data_7(&self) -> PGM_DATA_7_R {
        PGM_DATA_7_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PGM_DATA7")
            .field("pgm_data_7", &self.pgm_data_7())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Configures the 7th 32-bit data to be programmed."]
    #[inline(always)]
    pub fn pgm_data_7(&mut self) -> PGM_DATA_7_W<'_, PGM_DATA7_SPEC> {
        PGM_DATA_7_W::new(self, 0)
    }
}
#[doc = "Register 7 that stores data to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_data7::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_data7::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PGM_DATA7_SPEC;
impl crate::RegisterSpec for PGM_DATA7_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pgm_data7::R`](R) reader structure"]
impl crate::Readable for PGM_DATA7_SPEC {}
#[doc = "`write(|w| ..)` method takes [`pgm_data7::W`](W) writer structure"]
impl crate::Writable for PGM_DATA7_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PGM_DATA7 to value 0"]
impl crate::Resettable for PGM_DATA7_SPEC {}
