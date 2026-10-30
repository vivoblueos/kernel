#[doc = "Register `GEN_TSTMP_A` reader"]
pub type R = crate::R<GEN_TSTMP_A_SPEC>;
#[doc = "Register `GEN_TSTMP_A` writer"]
pub type W = crate::W<GEN_TSTMP_A_SPEC>;
#[doc = "Field `A` reader - PWM generator 0 time stamp A's shadow register"]
pub type A_R = crate::FieldReader<u16>;
#[doc = "Field `A` writer - PWM generator 0 time stamp A's shadow register"]
pub type A_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - PWM generator 0 time stamp A's shadow register"]
    #[inline(always)]
    pub fn a(&self) -> A_R {
        A_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("GEN_TSTMP_A").field("a", &self.a()).finish()
    }
}
impl W {
    #[doc = "Bits 0:15 - PWM generator 0 time stamp A's shadow register"]
    #[inline(always)]
    pub fn a(&mut self) -> A_W<'_, GEN_TSTMP_A_SPEC> {
        A_W::new(self, 0)
    }
}
#[doc = "Shadow register for register A.\n\nYou can [`read`](crate::Reg::read) this register and get [`gen_tstmp_a::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`gen_tstmp_a::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GEN_TSTMP_A_SPEC;
impl crate::RegisterSpec for GEN_TSTMP_A_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`gen_tstmp_a::R`](R) reader structure"]
impl crate::Readable for GEN_TSTMP_A_SPEC {}
#[doc = "`write(|w| ..)` method takes [`gen_tstmp_a::W`](W) writer structure"]
impl crate::Writable for GEN_TSTMP_A_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets GEN_TSTMP_A to value 0"]
impl crate::Resettable for GEN_TSTMP_A_SPEC {}
