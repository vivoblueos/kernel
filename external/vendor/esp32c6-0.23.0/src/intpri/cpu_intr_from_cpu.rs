#[doc = "Register `CPU_INTR_FROM_CPU%s` reader"]
pub type R = crate::R<CPU_INTR_FROM_CPU_SPEC>;
#[doc = "Register `CPU_INTR_FROM_CPU%s` writer"]
pub type W = crate::W<CPU_INTR_FROM_CPU_SPEC>;
#[doc = "Field `CPU_INTR` reader - Need add description"]
pub type CPU_INTR_R = crate::BitReader;
#[doc = "Field `CPU_INTR` writer - Need add description"]
pub type CPU_INTR_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Need add description"]
    #[inline(always)]
    pub fn cpu_intr(&self) -> CPU_INTR_R {
        CPU_INTR_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CPU_INTR_FROM_CPU")
            .field("cpu_intr", &self.cpu_intr())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Need add description"]
    #[inline(always)]
    pub fn cpu_intr(&mut self) -> CPU_INTR_W<'_, CPU_INTR_FROM_CPU_SPEC> {
        CPU_INTR_W::new(self, 0)
    }
}
#[doc = "register description\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_intr_from_cpu::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_intr_from_cpu::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CPU_INTR_FROM_CPU_SPEC;
impl crate::RegisterSpec for CPU_INTR_FROM_CPU_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cpu_intr_from_cpu::R`](R) reader structure"]
impl crate::Readable for CPU_INTR_FROM_CPU_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cpu_intr_from_cpu::W`](W) writer structure"]
impl crate::Writable for CPU_INTR_FROM_CPU_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CPU_INTR_FROM_CPU%s to value 0"]
impl crate::Resettable for CPU_INTR_FROM_CPU_SPEC {}
