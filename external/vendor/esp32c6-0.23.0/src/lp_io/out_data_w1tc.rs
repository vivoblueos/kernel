#[doc = "Register `OUT_DATA_W1TC` writer"]
pub type W = crate::W<OUT_DATA_W1TC_SPEC>;
#[doc = "Field `OUT_DATA_W1TC` writer - clear one time output data"]
pub type OUT_DATA_W1TC_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<OUT_DATA_W1TC_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bits 0:7 - clear one time output data"]
    #[inline(always)]
    pub fn out_data_w1tc(&mut self) -> OUT_DATA_W1TC_W<'_, OUT_DATA_W1TC_SPEC> {
        OUT_DATA_W1TC_W::new(self, 0)
    }
}
#[doc = "need des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_data_w1tc::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OUT_DATA_W1TC_SPEC;
impl crate::RegisterSpec for OUT_DATA_W1TC_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`out_data_w1tc::W`](W) writer structure"]
impl crate::Writable for OUT_DATA_W1TC_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets OUT_DATA_W1TC to value 0"]
impl crate::Resettable for OUT_DATA_W1TC_SPEC {}
