#[doc = "Register `INT_ST` reader"]
pub type R = crate::R<INT_ST_SPEC>;
#[doc = "Field `READ_DONE` reader - The status signal for read_done interrupt."]
pub type READ_DONE_R = crate::BitReader;
#[doc = "Field `PGM_DONE` reader - The status signal for pgm_done interrupt."]
pub type PGM_DONE_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The status signal for read_done interrupt."]
    #[inline(always)]
    pub fn read_done(&self) -> READ_DONE_R {
        READ_DONE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The status signal for pgm_done interrupt."]
    #[inline(always)]
    pub fn pgm_done(&self) -> PGM_DONE_R {
        PGM_DONE_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_ST")
            .field("read_done", &self.read_done())
            .field("pgm_done", &self.pgm_done())
            .finish()
    }
}
#[doc = "eFuse interrupt status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_ST_SPEC;
impl crate::RegisterSpec for INT_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_st::R`](R) reader structure"]
impl crate::Readable for INT_ST_SPEC {}
#[doc = "`reset()` method sets INT_ST to value 0"]
impl crate::Resettable for INT_ST_SPEC {}
