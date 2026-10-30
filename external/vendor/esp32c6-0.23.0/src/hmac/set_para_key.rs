#[doc = "Register `SET_PARA_KEY` writer"]
pub type W = crate::W<SET_PARA_KEY_SPEC>;
#[doc = "Field `KEY_SET` writer - Set hmac parameter key."]
pub type KEY_SET_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SET_PARA_KEY_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bits 0:2 - Set hmac parameter key."]
    #[inline(always)]
    pub fn key_set(&mut self) -> KEY_SET_W<'_, SET_PARA_KEY_SPEC> {
        KEY_SET_W::new(self, 0)
    }
}
#[doc = "Configure key.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`set_para_key::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SET_PARA_KEY_SPEC;
impl crate::RegisterSpec for SET_PARA_KEY_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`set_para_key::W`](W) writer structure"]
impl crate::Writable for SET_PARA_KEY_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SET_PARA_KEY to value 0"]
impl crate::Resettable for SET_PARA_KEY_SPEC {}
