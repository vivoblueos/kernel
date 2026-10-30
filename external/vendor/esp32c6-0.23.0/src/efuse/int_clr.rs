#[doc = "Register `INT_CLR` writer"]
pub type W = crate::W<INT_CLR_SPEC>;
#[doc = "Field `READ_DONE` writer - The clear signal for read_done interrupt."]
pub type READ_DONE_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `PGM_DONE` writer - The clear signal for pgm_done interrupt."]
pub type PGM_DONE_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<INT_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - The clear signal for read_done interrupt."]
    #[inline(always)]
    pub fn read_done(&mut self) -> READ_DONE_W<'_, INT_CLR_SPEC> {
        READ_DONE_W::new(self, 0)
    }
    #[doc = "Bit 1 - The clear signal for pgm_done interrupt."]
    #[inline(always)]
    pub fn pgm_done(&mut self) -> PGM_DONE_W<'_, INT_CLR_SPEC> {
        PGM_DONE_W::new(self, 1)
    }
}
#[doc = "eFuse interrupt clear register.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_CLR_SPEC;
impl crate::RegisterSpec for INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`int_clr::W`](W) writer structure"]
impl crate::Writable for INT_CLR_SPEC {
    type Safety = crate::Unsafe;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0x03;
}
#[doc = "`reset()` method sets INT_CLR to value 0"]
impl crate::Resettable for INT_CLR_SPEC {}
