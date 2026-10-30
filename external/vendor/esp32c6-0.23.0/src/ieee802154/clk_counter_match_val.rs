#[doc = "Register `CLK_COUNTER_MATCH_VAL` reader"]
pub type R = crate::R<CLK_COUNTER_MATCH_VAL_SPEC>;
#[doc = "Register `CLK_COUNTER_MATCH_VAL` writer"]
pub type W = crate::W<CLK_COUNTER_MATCH_VAL_SPEC>;
#[doc = "Field `CLK_COUNT_MATCH_VAL` reader - "]
pub type CLK_COUNT_MATCH_VAL_R = crate::FieldReader<u16>;
#[doc = "Field `CLK_COUNT_MATCH_VAL` writer - "]
pub type CLK_COUNT_MATCH_VAL_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn clk_count_match_val(&self) -> CLK_COUNT_MATCH_VAL_R {
        CLK_COUNT_MATCH_VAL_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLK_COUNTER_MATCH_VAL")
            .field("clk_count_match_val", &self.clk_count_match_val())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn clk_count_match_val(&mut self) -> CLK_COUNT_MATCH_VAL_W<'_, CLK_COUNTER_MATCH_VAL_SPEC> {
        CLK_COUNT_MATCH_VAL_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_counter_match_val::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_counter_match_val::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLK_COUNTER_MATCH_VAL_SPEC;
impl crate::RegisterSpec for CLK_COUNTER_MATCH_VAL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clk_counter_match_val::R`](R) reader structure"]
impl crate::Readable for CLK_COUNTER_MATCH_VAL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clk_counter_match_val::W`](W) writer structure"]
impl crate::Writable for CLK_COUNTER_MATCH_VAL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLK_COUNTER_MATCH_VAL to value 0"]
impl crate::Resettable for CLK_COUNTER_MATCH_VAL_SPEC {}
