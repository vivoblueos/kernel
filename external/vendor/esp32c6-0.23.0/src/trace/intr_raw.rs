#[doc = "Register `INTR_RAW` reader"]
pub type R = crate::R<INTR_RAW_SPEC>;
#[doc = "Field `FIFO_OVERFLOW_INTR_RAW` reader - fifo_overflow interrupt status"]
pub type FIFO_OVERFLOW_INTR_RAW_R = crate::BitReader;
#[doc = "Field `MEM_FULL_INTR_RAW` reader - mem_full interrupt status"]
pub type MEM_FULL_INTR_RAW_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - fifo_overflow interrupt status"]
    #[inline(always)]
    pub fn fifo_overflow_intr_raw(&self) -> FIFO_OVERFLOW_INTR_RAW_R {
        FIFO_OVERFLOW_INTR_RAW_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - mem_full interrupt status"]
    #[inline(always)]
    pub fn mem_full_intr_raw(&self) -> MEM_FULL_INTR_RAW_R {
        MEM_FULL_INTR_RAW_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INTR_RAW")
            .field("fifo_overflow_intr_raw", &self.fifo_overflow_intr_raw())
            .field("mem_full_intr_raw", &self.mem_full_intr_raw())
            .finish()
    }
}
#[doc = "interrupt status register\n\nYou can [`read`](crate::Reg::read) this register and get [`intr_raw::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INTR_RAW_SPEC;
impl crate::RegisterSpec for INTR_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`intr_raw::R`](R) reader structure"]
impl crate::Readable for INTR_RAW_SPEC {}
#[doc = "`reset()` method sets INTR_RAW to value 0"]
impl crate::Resettable for INTR_RAW_SPEC {}
