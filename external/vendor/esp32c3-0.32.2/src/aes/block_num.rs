#[doc = "Register `BLOCK_NUM` reader"]
pub type R = crate::R<BLOCK_NUM_SPEC>;
#[doc = "Register `BLOCK_NUM` writer"]
pub type W = crate::W<BLOCK_NUM_SPEC>;
#[doc = "Field `BLOCK_NUM` reader - Those bits stores the number of Plaintext/ciphertext block."]
pub type BLOCK_NUM_R = crate::FieldReader<u32>;
#[doc = "Field `BLOCK_NUM` writer - Those bits stores the number of Plaintext/ciphertext block."]
pub type BLOCK_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Those bits stores the number of Plaintext/ciphertext block."]
    #[inline(always)]
    pub fn block_num(&self) -> BLOCK_NUM_R {
        BLOCK_NUM_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLOCK_NUM")
            .field("block_num", &self.block_num())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Those bits stores the number of Plaintext/ciphertext block."]
    #[inline(always)]
    pub fn block_num(&mut self) -> BLOCK_NUM_W<'_, BLOCK_NUM_SPEC> {
        BLOCK_NUM_W::new(self, 0)
    }
}
#[doc = "AES block number register\n\nYou can [`read`](crate::Reg::read) this register and get [`block_num::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`block_num::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLOCK_NUM_SPEC;
impl crate::RegisterSpec for BLOCK_NUM_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`block_num::R`](R) reader structure"]
impl crate::Readable for BLOCK_NUM_SPEC {}
#[doc = "`write(|w| ..)` method takes [`block_num::W`](W) writer structure"]
impl crate::Writable for BLOCK_NUM_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets BLOCK_NUM to value 0"]
impl crate::Resettable for BLOCK_NUM_SPEC {}
