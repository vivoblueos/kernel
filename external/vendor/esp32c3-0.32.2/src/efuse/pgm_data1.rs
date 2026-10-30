#[doc = "Register `PGM_DATA1` reader"]
pub type R = crate::R<PGM_DATA1_SPEC>;
#[doc = "Register `PGM_DATA1` writer"]
pub type W = crate::W<PGM_DATA1_SPEC>;
#[doc = "Field `PGM_DATA_1` reader - The content of the 1st 32-bit data to be programmed."]
pub type PGM_DATA_1_R = crate::FieldReader<u32>;
#[doc = "Field `PGM_DATA_1` writer - The content of the 1st 32-bit data to be programmed."]
pub type PGM_DATA_1_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - The content of the 1st 32-bit data to be programmed."]
    #[inline(always)]
    pub fn pgm_data_1(&self) -> PGM_DATA_1_R {
        PGM_DATA_1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PGM_DATA1")
            .field("pgm_data_1", &self.pgm_data_1())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - The content of the 1st 32-bit data to be programmed."]
    #[inline(always)]
    pub fn pgm_data_1(&mut self) -> PGM_DATA_1_W<'_, PGM_DATA1_SPEC> {
        PGM_DATA_1_W::new(self, 0)
    }
}
#[doc = "Register 1 that stores data to be programmed.\n\nYou can [`read`](crate::Reg::read) this register and get [`pgm_data1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pgm_data1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PGM_DATA1_SPEC;
impl crate::RegisterSpec for PGM_DATA1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pgm_data1::R`](R) reader structure"]
impl crate::Readable for PGM_DATA1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`pgm_data1::W`](W) writer structure"]
impl crate::Writable for PGM_DATA1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PGM_DATA1 to value 0"]
impl crate::Resettable for PGM_DATA1_SPEC {}
