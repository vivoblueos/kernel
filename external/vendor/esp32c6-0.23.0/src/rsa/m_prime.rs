#[doc = "Register `M_PRIME` reader"]
pub type R = crate::R<M_PRIME_SPEC>;
#[doc = "Register `M_PRIME` writer"]
pub type W = crate::W<M_PRIME_SPEC>;
#[doc = "Field `M_PRIME` reader - Those bits stores m'"]
pub type M_PRIME_R = crate::FieldReader<u32>;
#[doc = "Field `M_PRIME` writer - Those bits stores m'"]
pub type M_PRIME_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Those bits stores m'"]
    #[inline(always)]
    pub fn m_prime(&self) -> M_PRIME_R {
        M_PRIME_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("M_PRIME")
            .field("m_prime", &self.m_prime())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Those bits stores m'"]
    #[inline(always)]
    pub fn m_prime(&mut self) -> M_PRIME_W<'_, M_PRIME_SPEC> {
        M_PRIME_W::new(self, 0)
    }
}
#[doc = "RSA M_prime register\n\nYou can [`read`](crate::Reg::read) this register and get [`m_prime::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`m_prime::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct M_PRIME_SPEC;
impl crate::RegisterSpec for M_PRIME_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`m_prime::R`](R) reader structure"]
impl crate::Readable for M_PRIME_SPEC {}
#[doc = "`write(|w| ..)` method takes [`m_prime::W`](W) writer structure"]
impl crate::Writable for M_PRIME_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets M_PRIME to value 0"]
impl crate::Resettable for M_PRIME_SPEC {}
