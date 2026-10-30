#[doc = "Register `CPU_INT_THRESH` reader"]
pub type R = crate::R<CPU_INT_THRESH_SPEC>;
#[doc = "Register `CPU_INT_THRESH` writer"]
pub type W = crate::W<CPU_INT_THRESH_SPEC>;
#[doc = "Field `CPU_INT_THRESH` reader - reg_core0_cpu_int_thresh"]
pub type CPU_INT_THRESH_R = crate::FieldReader;
#[doc = "Field `CPU_INT_THRESH` writer - reg_core0_cpu_int_thresh"]
pub type CPU_INT_THRESH_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3 - reg_core0_cpu_int_thresh"]
    #[inline(always)]
    pub fn cpu_int_thresh(&self) -> CPU_INT_THRESH_R {
        CPU_INT_THRESH_R::new((self.bits & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CPU_INT_THRESH")
            .field("cpu_int_thresh", &self.cpu_int_thresh())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3 - reg_core0_cpu_int_thresh"]
    #[inline(always)]
    pub fn cpu_int_thresh(&mut self) -> CPU_INT_THRESH_W<'_, CPU_INT_THRESH_SPEC> {
        CPU_INT_THRESH_W::new(self, 0)
    }
}
#[doc = "mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_int_thresh::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_int_thresh::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CPU_INT_THRESH_SPEC;
impl crate::RegisterSpec for CPU_INT_THRESH_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cpu_int_thresh::R`](R) reader structure"]
impl crate::Readable for CPU_INT_THRESH_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cpu_int_thresh::W`](W) writer structure"]
impl crate::Writable for CPU_INT_THRESH_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CPU_INT_THRESH to value 0"]
impl crate::Resettable for CPU_INT_THRESH_SPEC {}
