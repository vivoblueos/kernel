#[doc = "Register `INTR_CLR` writer"]
pub type W = crate::W<INTR_CLR_SPEC>;
#[doc = "Field `FIFO_OVERFLOW_INTR_CLR` writer - Set 1 clr fifo overflow interrupt"]
pub type FIFO_OVERFLOW_INTR_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MEM_FULL_INTR_CLR` writer - Set 1 clr mem full interrupt"]
pub type MEM_FULL_INTR_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<INTR_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 clr fifo overflow interrupt"]
    #[inline(always)]
    pub fn fifo_overflow_intr_clr(&mut self) -> FIFO_OVERFLOW_INTR_CLR_W<'_, INTR_CLR_SPEC> {
        FIFO_OVERFLOW_INTR_CLR_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 1 clr mem full interrupt"]
    #[inline(always)]
    pub fn mem_full_intr_clr(&mut self) -> MEM_FULL_INTR_CLR_W<'_, INTR_CLR_SPEC> {
        MEM_FULL_INTR_CLR_W::new(self, 1)
    }
}
#[doc = "interrupt clear register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`intr_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INTR_CLR_SPEC;
impl crate::RegisterSpec for INTR_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`intr_clr::W`](W) writer structure"]
impl crate::Writable for INTR_CLR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INTR_CLR to value 0"]
impl crate::Resettable for INTR_CLR_SPEC {}
