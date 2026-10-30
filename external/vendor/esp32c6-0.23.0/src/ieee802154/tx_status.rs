#[doc = "Register `TX_STATUS` reader"]
pub type R = crate::R<TX_STATUS_SPEC>;
#[doc = "Register `TX_STATUS` writer"]
pub type W = crate::W<TX_STATUS_SPEC>;
#[doc = "Field `TX_STATE` reader - "]
pub type TX_STATE_R = crate::FieldReader;
#[doc = "Field `TX_STATE` writer - "]
pub type TX_STATE_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `TX_ABORT_STATUS` reader - "]
pub type TX_ABORT_STATUS_R = crate::FieldReader;
#[doc = "Field `TX_ABORT_STATUS` writer - "]
pub type TX_ABORT_STATUS_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `TX_SEC_ERROR_CODE` reader - "]
pub type TX_SEC_ERROR_CODE_R = crate::FieldReader;
#[doc = "Field `TX_SEC_ERROR_CODE` writer - "]
pub type TX_SEC_ERROR_CODE_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn tx_state(&self) -> TX_STATE_R {
        TX_STATE_R::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:8"]
    #[inline(always)]
    pub fn tx_abort_status(&self) -> TX_ABORT_STATUS_R {
        TX_ABORT_STATUS_R::new(((self.bits >> 4) & 0x1f) as u8)
    }
    #[doc = "Bits 16:19"]
    #[inline(always)]
    pub fn tx_sec_error_code(&self) -> TX_SEC_ERROR_CODE_R {
        TX_SEC_ERROR_CODE_R::new(((self.bits >> 16) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_STATUS")
            .field("tx_state", &self.tx_state())
            .field("tx_abort_status", &self.tx_abort_status())
            .field("tx_sec_error_code", &self.tx_sec_error_code())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn tx_state(&mut self) -> TX_STATE_W<'_, TX_STATUS_SPEC> {
        TX_STATE_W::new(self, 0)
    }
    #[doc = "Bits 4:8"]
    #[inline(always)]
    pub fn tx_abort_status(&mut self) -> TX_ABORT_STATUS_W<'_, TX_STATUS_SPEC> {
        TX_ABORT_STATUS_W::new(self, 4)
    }
    #[doc = "Bits 16:19"]
    #[inline(always)]
    pub fn tx_sec_error_code(&mut self) -> TX_SEC_ERROR_CODE_W<'_, TX_STATUS_SPEC> {
        TX_SEC_ERROR_CODE_W::new(self, 16)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_status::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_status::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_STATUS_SPEC;
impl crate::RegisterSpec for TX_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_status::R`](R) reader structure"]
impl crate::Readable for TX_STATUS_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_status::W`](W) writer structure"]
impl crate::Writable for TX_STATUS_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_STATUS to value 0"]
impl crate::Resettable for TX_STATUS_SPEC {}
