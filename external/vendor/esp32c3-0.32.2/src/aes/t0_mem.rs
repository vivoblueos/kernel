#[doc = "Register `T0_MEM[%s]` reader"]
pub type R = crate::R<T0_MEM_SPEC>;
#[doc = "Register `T0_MEM[%s]` writer"]
pub type W = crate::W<T0_MEM_SPEC>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}", self.bits())
    }
}
impl W {}
#[doc = "The memory that stores T0\n\nYou can [`read`](crate::Reg::read) this register and get [`t0_mem::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`t0_mem::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct T0_MEM_SPEC;
impl crate::RegisterSpec for T0_MEM_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`t0_mem::R`](R) reader structure"]
impl crate::Readable for T0_MEM_SPEC {}
#[doc = "`write(|w| ..)` method takes [`t0_mem::W`](W) writer structure"]
impl crate::Writable for T0_MEM_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets T0_MEM[%s] to value 0"]
impl crate::Resettable for T0_MEM_SPEC {}
