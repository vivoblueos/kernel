#[doc = "Register `Y_MEM[%s]` reader"]
pub type R = crate::R<Y_MEM_SPEC>;
#[doc = "Register `Y_MEM[%s]` writer"]
pub type W = crate::W<Y_MEM_SPEC>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}", self.bits())
    }
}
impl W {}
#[doc = "memory that stores Y\n\nYou can [`read`](crate::Reg::read) this register and get [`y_mem::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`y_mem::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Y_MEM_SPEC;
impl crate::RegisterSpec for Y_MEM_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`y_mem::R`](R) reader structure"]
impl crate::Readable for Y_MEM_SPEC {}
#[doc = "`write(|w| ..)` method takes [`y_mem::W`](W) writer structure"]
impl crate::Writable for Y_MEM_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets Y_MEM[%s] to value 0"]
impl crate::Resettable for Y_MEM_SPEC {}
