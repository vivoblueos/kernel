#[doc = "Register `CPU_INT_TYPE` reader"]
pub type R = crate::R<CPU_INT_TYPE_SPEC>;
#[doc = "Register `CPU_INT_TYPE` writer"]
pub type W = crate::W<CPU_INT_TYPE_SPEC>;
#[doc = "Field `CPU_INT_TYPE` reader - reg_core0_cpu_int_type"]
pub type CPU_INT_TYPE_R = crate::FieldReader<u32>;
#[doc = "Field `CPU_INT_TYPE` writer - reg_core0_cpu_int_type"]
pub type CPU_INT_TYPE_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - reg_core0_cpu_int_type"]
    #[inline(always)]
    pub fn cpu_int_type(&self) -> CPU_INT_TYPE_R {
        CPU_INT_TYPE_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CPU_INT_TYPE")
            .field("cpu_int_type", &self.cpu_int_type())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - reg_core0_cpu_int_type"]
    #[inline(always)]
    pub fn cpu_int_type(&mut self) -> CPU_INT_TYPE_W<'_, CPU_INT_TYPE_SPEC> {
        CPU_INT_TYPE_W::new(self, 0)
    }
}
#[doc = "mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_int_type::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_int_type::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CPU_INT_TYPE_SPEC;
impl crate::RegisterSpec for CPU_INT_TYPE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cpu_int_type::R`](R) reader structure"]
impl crate::Readable for CPU_INT_TYPE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cpu_int_type::W`](W) writer structure"]
impl crate::Writable for CPU_INT_TYPE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CPU_INT_TYPE to value 0"]
impl crate::Resettable for CPU_INT_TYPE_SPEC {}
