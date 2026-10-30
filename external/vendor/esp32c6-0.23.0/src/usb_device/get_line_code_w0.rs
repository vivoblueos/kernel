#[doc = "Register `GET_LINE_CODE_W0` reader"]
pub type R = crate::R<GET_LINE_CODE_W0_SPEC>;
#[doc = "Register `GET_LINE_CODE_W0` writer"]
pub type W = crate::W<GET_LINE_CODE_W0_SPEC>;
#[doc = "Field `GET_DW_DTE_RATE` reader - The value of dwDTERate set by software which is requested by GET_LINE_CODING command."]
pub type GET_DW_DTE_RATE_R = crate::FieldReader<u32>;
#[doc = "Field `GET_DW_DTE_RATE` writer - The value of dwDTERate set by software which is requested by GET_LINE_CODING command."]
pub type GET_DW_DTE_RATE_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - The value of dwDTERate set by software which is requested by GET_LINE_CODING command."]
    #[inline(always)]
    pub fn get_dw_dte_rate(&self) -> GET_DW_DTE_RATE_R {
        GET_DW_DTE_RATE_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("GET_LINE_CODE_W0")
            .field("get_dw_dte_rate", &self.get_dw_dte_rate())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - The value of dwDTERate set by software which is requested by GET_LINE_CODING command."]
    #[inline(always)]
    pub fn get_dw_dte_rate(&mut self) -> GET_DW_DTE_RATE_W<'_, GET_LINE_CODE_W0_SPEC> {
        GET_DW_DTE_RATE_W::new(self, 0)
    }
}
#[doc = "W0 of GET_LINE_CODING command.\n\nYou can [`read`](crate::Reg::read) this register and get [`get_line_code_w0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`get_line_code_w0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GET_LINE_CODE_W0_SPEC;
impl crate::RegisterSpec for GET_LINE_CODE_W0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`get_line_code_w0::R`](R) reader structure"]
impl crate::Readable for GET_LINE_CODE_W0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`get_line_code_w0::W`](W) writer structure"]
impl crate::Writable for GET_LINE_CODE_W0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets GET_LINE_CODE_W0 to value 0"]
impl crate::Resettable for GET_LINE_CODE_W0_SPEC {}
