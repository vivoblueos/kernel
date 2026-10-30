#[doc = "Register `AAD_BLOCK_NUM` reader"]
pub type R = crate::R<AAD_BLOCK_NUM_SPEC>;
#[doc = "Register `AAD_BLOCK_NUM` writer"]
pub type W = crate::W<AAD_BLOCK_NUM_SPEC>;
#[doc = "Field `AAD_BLOCK_NUM` reader - Those bits stores the number of AAD block."]
pub type AAD_BLOCK_NUM_R = crate::FieldReader<u32>;
#[doc = "Field `AAD_BLOCK_NUM` writer - Those bits stores the number of AAD block."]
pub type AAD_BLOCK_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Those bits stores the number of AAD block."]
    #[inline(always)]
    pub fn aad_block_num(&self) -> AAD_BLOCK_NUM_R {
        AAD_BLOCK_NUM_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("AAD_BLOCK_NUM")
            .field("aad_block_num", &self.aad_block_num())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Those bits stores the number of AAD block."]
    #[inline(always)]
    pub fn aad_block_num(&mut self) -> AAD_BLOCK_NUM_W<'_, AAD_BLOCK_NUM_SPEC> {
        AAD_BLOCK_NUM_W::new(self, 0)
    }
}
#[doc = "Additional Authential Data block number register\n\nYou can [`read`](crate::Reg::read) this register and get [`aad_block_num::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`aad_block_num::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AAD_BLOCK_NUM_SPEC;
impl crate::RegisterSpec for AAD_BLOCK_NUM_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`aad_block_num::R`](R) reader structure"]
impl crate::Readable for AAD_BLOCK_NUM_SPEC {}
#[doc = "`write(|w| ..)` method takes [`aad_block_num::W`](W) writer structure"]
impl crate::Writable for AAD_BLOCK_NUM_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets AAD_BLOCK_NUM to value 0"]
impl crate::Resettable for AAD_BLOCK_NUM_SPEC {}
