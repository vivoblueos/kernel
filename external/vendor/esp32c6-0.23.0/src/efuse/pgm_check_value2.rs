#[doc = "Register `PGM_CHECK_VALUE2` reader"]
pub type R = crate::R<PGM_CHECK_VALUE2_SPEC>;
#[doc = "Register `PGM_CHECK_VALUE2` writer"]
pub type W = crate::W<PGM_CHECK_VALUE2_SPEC>;
#[doc = "Field `PGM_RS_DATA_2` reader - Configures the 2nd 32-bit RS code to be programmed."]
pub type PGM_RS_DATA_2_R = crate::FieldReader<u32>;
#[doc = "Field `PGM_RS_DATA_2` writer - Configures the 2nd 32-bit RS code to be programmed."]
pub type PGM_RS_DATA_2_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Configures the 2nd 32-bit RS code to be programmed."]
    #[inline(always)]
    pub fn pgm_rs_data_2(&self) -> PGM_RS_DATA_2_R {
        PGM_RS_DATA_2_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PGM_CHECK_VALUE2")
            .field("pgm_rs_data_2", &self.pgm_rs_data_2())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Configures the 2nd 32-bit RS code to be programmed."]
    #[inline(always)]
    pub fn pgm_rs_data_2(&mut self) -> PGM_RS_DATA_2_W<'_, PGM_CHECK_VALUE2_SPEC> {
        PGM_RS_DATA_2_W::new(self, 0)
    }
}
#[doc = "Register 2 that stores the RS code to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_check_value2::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_check_value2::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PGM_CHECK_VALUE2_SPEC;
impl crate::RegisterSpec for PGM_CHECK_VALUE2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pgm_check_value2::R`](R) reader structure"]
impl crate::Readable for PGM_CHECK_VALUE2_SPEC {}
#[doc = "`write(|w| ..)` method takes [`pgm_check_value2::W`](W) writer structure"]
impl crate::Writable for PGM_CHECK_VALUE2_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PGM_CHECK_VALUE2 to value 0"]
impl crate::Resettable for PGM_CHECK_VALUE2_SPEC {}
