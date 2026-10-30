#[doc = "Register `K_MEM[%s]` reader"]
pub type R = crate::R<K_MEM_SPEC>;
#[doc = "Register `K_MEM[%s]` writer"]
pub type W = crate::W<K_MEM_SPEC>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}", self.bits())
    }
}
impl W {}
#[doc = "The memory that stores k.\n\nYou can [`read`](crate::Reg::read) this register and get [`k_mem::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`k_mem::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct K_MEM_SPEC;
impl crate::RegisterSpec for K_MEM_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`k_mem::R`](R) reader structure"]
impl crate::Readable for K_MEM_SPEC {}
#[doc = "`write(|w| ..)` method takes [`k_mem::W`](W) writer structure"]
impl crate::Writable for K_MEM_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets K_MEM[%s] to value 0"]
impl crate::Resettable for K_MEM_SPEC {}
