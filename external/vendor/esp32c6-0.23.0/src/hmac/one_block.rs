#[doc = "Register `ONE_BLOCK` writer"]
pub type W = crate::W<ONE_BLOCK_SPEC>;
#[doc = "Field `SET_ONE_BLOCK` writer - Don't have to do padding."]
pub type SET_ONE_BLOCK_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<ONE_BLOCK_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Don't have to do padding."]
    #[inline(always)]
    pub fn set_one_block(&mut self) -> SET_ONE_BLOCK_W<'_, ONE_BLOCK_SPEC> {
        SET_ONE_BLOCK_W::new(self, 0)
    }
}
#[doc = "Process control register 6.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`one_block::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ONE_BLOCK_SPEC;
impl crate::RegisterSpec for ONE_BLOCK_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`one_block::W`](W) writer structure"]
impl crate::Writable for ONE_BLOCK_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ONE_BLOCK to value 0"]
impl crate::Resettable for ONE_BLOCK_SPEC {}
