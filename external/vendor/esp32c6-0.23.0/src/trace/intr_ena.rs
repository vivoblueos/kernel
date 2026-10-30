#[doc = "Register `INTR_ENA` reader"]
pub type R = crate::R<INTR_ENA_SPEC>;
#[doc = "Register `INTR_ENA` writer"]
pub type W = crate::W<INTR_ENA_SPEC>;
#[doc = "Field `FIFO_OVERFLOW_INTR_ENA` reader - Set 1 enable fifo_overflow interrupt"]
pub type FIFO_OVERFLOW_INTR_ENA_R = crate::BitReader;
#[doc = "Field `FIFO_OVERFLOW_INTR_ENA` writer - Set 1 enable fifo_overflow interrupt"]
pub type FIFO_OVERFLOW_INTR_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MEM_FULL_INTR_ENA` reader - Set 1 enable mem_full interrupt"]
pub type MEM_FULL_INTR_ENA_R = crate::BitReader;
#[doc = "Field `MEM_FULL_INTR_ENA` writer - Set 1 enable mem_full interrupt"]
pub type MEM_FULL_INTR_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 enable fifo_overflow interrupt"]
    #[inline(always)]
    pub fn fifo_overflow_intr_ena(&self) -> FIFO_OVERFLOW_INTR_ENA_R {
        FIFO_OVERFLOW_INTR_ENA_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 1 enable mem_full interrupt"]
    #[inline(always)]
    pub fn mem_full_intr_ena(&self) -> MEM_FULL_INTR_ENA_R {
        MEM_FULL_INTR_ENA_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INTR_ENA")
            .field("fifo_overflow_intr_ena", &self.fifo_overflow_intr_ena())
            .field("mem_full_intr_ena", &self.mem_full_intr_ena())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 enable fifo_overflow interrupt"]
    #[inline(always)]
    pub fn fifo_overflow_intr_ena(&mut self) -> FIFO_OVERFLOW_INTR_ENA_W<'_, INTR_ENA_SPEC> {
        FIFO_OVERFLOW_INTR_ENA_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 1 enable mem_full interrupt"]
    #[inline(always)]
    pub fn mem_full_intr_ena(&mut self) -> MEM_FULL_INTR_ENA_W<'_, INTR_ENA_SPEC> {
        MEM_FULL_INTR_ENA_W::new(self, 1)
    }
}
#[doc = "interrupt enable register\n\nYou can [`read`](crate::Reg::read) this register and get [`intr_ena::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`intr_ena::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INTR_ENA_SPEC;
impl crate::RegisterSpec for INTR_ENA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`intr_ena::R`](R) reader structure"]
impl crate::Readable for INTR_ENA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`intr_ena::W`](W) writer structure"]
impl crate::Writable for INTR_ENA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INTR_ENA to value 0"]
impl crate::Resettable for INTR_ENA_SPEC {}
