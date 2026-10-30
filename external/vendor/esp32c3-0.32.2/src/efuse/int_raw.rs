#[doc = "Register `INT_RAW` reader"]
pub type R = crate::R<INT_RAW_SPEC>;
#[doc = "Register `INT_RAW` writer"]
pub type W = crate::W<INT_RAW_SPEC>;
#[doc = "Field `READ_DONE` reader - The raw bit signal for read_done interrupt."]
pub type READ_DONE_R = crate::BitReader;
#[doc = "Field `READ_DONE` writer - The raw bit signal for read_done interrupt."]
pub type READ_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PGM_DONE` reader - The raw bit signal for pgm_done interrupt."]
pub type PGM_DONE_R = crate::BitReader;
#[doc = "Field `PGM_DONE` writer - The raw bit signal for pgm_done interrupt."]
pub type PGM_DONE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The raw bit signal for read_done interrupt."]
    #[inline(always)]
    pub fn read_done(&self) -> READ_DONE_R {
        READ_DONE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The raw bit signal for pgm_done interrupt."]
    #[inline(always)]
    pub fn pgm_done(&self) -> PGM_DONE_R {
        PGM_DONE_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_RAW")
            .field("read_done", &self.read_done())
            .field("pgm_done", &self.pgm_done())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The raw bit signal for read_done interrupt."]
    #[inline(always)]
    pub fn read_done(&mut self) -> READ_DONE_W<'_, INT_RAW_SPEC> {
        READ_DONE_W::new(self, 0)
    }
    #[doc = "Bit 1 - The raw bit signal for pgm_done interrupt."]
    #[inline(always)]
    pub fn pgm_done(&mut self) -> PGM_DONE_W<'_, INT_RAW_SPEC> {
        PGM_DONE_W::new(self, 1)
    }
}
#[doc = "eFuse raw interrupt register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_raw::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_RAW_SPEC;
impl crate::RegisterSpec for INT_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_raw::R`](R) reader structure"]
impl crate::Readable for INT_RAW_SPEC {}
#[doc = "`write(|w| ..)` method takes [`int_raw::W`](W) writer structure"]
impl crate::Writable for INT_RAW_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_RAW to value 0"]
impl crate::Resettable for INT_RAW_SPEC {}
