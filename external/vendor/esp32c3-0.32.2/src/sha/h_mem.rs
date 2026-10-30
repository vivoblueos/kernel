#[doc = "Register `H_MEM[%s]` reader"]
pub type R = crate::R<H_MEM_SPEC>;
#[doc = "Register `H_MEM[%s]` writer"]
pub type W = crate::W<H_MEM_SPEC>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}", self.bits())
    }
}
impl W {}
#[doc = "Sha H memory which contains intermediate hash or finial hash.\n\nYou can [`read`](crate::Reg::read) this register and get [`h_mem::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`h_mem::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct H_MEM_SPEC;
impl crate::RegisterSpec for H_MEM_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`h_mem::R`](R) reader structure"]
impl crate::Readable for H_MEM_SPEC {}
#[doc = "`write(|w| ..)` method takes [`h_mem::W`](W) writer structure"]
impl crate::Writable for H_MEM_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets H_MEM[%s] to value 0"]
impl crate::Resettable for H_MEM_SPEC {}
