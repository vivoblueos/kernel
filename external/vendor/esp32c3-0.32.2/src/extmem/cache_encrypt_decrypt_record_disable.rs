#[doc = "Register `CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE` reader"]
pub type R = crate::R<CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE_SPEC>;
#[doc = "Register `CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE` writer"]
pub type W = crate::W<CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE_SPEC>;
#[doc = "Field `RECORD_DISABLE_DB_ENCRYPT` reader - Reserved."]
pub type RECORD_DISABLE_DB_ENCRYPT_R = crate::BitReader;
#[doc = "Field `RECORD_DISABLE_DB_ENCRYPT` writer - Reserved."]
pub type RECORD_DISABLE_DB_ENCRYPT_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RECORD_DISABLE_G0CB_DECRYPT` reader - Reserved."]
pub type RECORD_DISABLE_G0CB_DECRYPT_R = crate::BitReader;
#[doc = "Field `RECORD_DISABLE_G0CB_DECRYPT` writer - Reserved."]
pub type RECORD_DISABLE_G0CB_DECRYPT_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Reserved."]
    #[inline(always)]
    pub fn record_disable_db_encrypt(&self) -> RECORD_DISABLE_DB_ENCRYPT_R {
        RECORD_DISABLE_DB_ENCRYPT_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Reserved."]
    #[inline(always)]
    pub fn record_disable_g0cb_decrypt(&self) -> RECORD_DISABLE_G0CB_DECRYPT_R {
        RECORD_DISABLE_G0CB_DECRYPT_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE")
            .field(
                "record_disable_db_encrypt",
                &self.record_disable_db_encrypt(),
            )
            .field(
                "record_disable_g0cb_decrypt",
                &self.record_disable_g0cb_decrypt(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Reserved."]
    #[inline(always)]
    pub fn record_disable_db_encrypt(
        &mut self,
    ) -> RECORD_DISABLE_DB_ENCRYPT_W<'_, CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE_SPEC> {
        RECORD_DISABLE_DB_ENCRYPT_W::new(self, 0)
    }
    #[doc = "Bit 1 - Reserved."]
    #[inline(always)]
    pub fn record_disable_g0cb_decrypt(
        &mut self,
    ) -> RECORD_DISABLE_G0CB_DECRYPT_W<'_, CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE_SPEC> {
        RECORD_DISABLE_G0CB_DECRYPT_W::new(self, 1)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_encrypt_decrypt_record_disable::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_encrypt_decrypt_record_disable::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE_SPEC;
impl crate::RegisterSpec for CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_encrypt_decrypt_record_disable::R`](R) reader structure"]
impl crate::Readable for CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cache_encrypt_decrypt_record_disable::W`](W) writer structure"]
impl crate::Writable for CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE to value 0"]
impl crate::Resettable for CACHE_ENCRYPT_DECRYPT_RECORD_DISABLE_SPEC {}
