#[doc = "Register `CLK_COUNTER` reader"]
pub type R = crate::R<CLK_COUNTER_SPEC>;
#[doc = "Register `CLK_COUNTER` writer"]
pub type W = crate::W<CLK_COUNTER_SPEC>;
#[doc = "Field `CLK_625US_CNT` reader - "]
pub type CLK_625US_CNT_R = crate::FieldReader<u16>;
#[doc = "Field `CLK_625US_CNT` writer - "]
pub type CLK_625US_CNT_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn clk_625us_cnt(&self) -> CLK_625US_CNT_R {
        CLK_625US_CNT_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLK_COUNTER")
            .field("clk_625us_cnt", &self.clk_625us_cnt())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:15"]
    #[inline(always)]
    pub fn clk_625us_cnt(&mut self) -> CLK_625US_CNT_W<'_, CLK_COUNTER_SPEC> {
        CLK_625US_CNT_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_counter::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_counter::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLK_COUNTER_SPEC;
impl crate::RegisterSpec for CLK_COUNTER_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clk_counter::R`](R) reader structure"]
impl crate::Readable for CLK_COUNTER_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clk_counter::W`](W) writer structure"]
impl crate::Writable for CLK_COUNTER_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLK_COUNTER to value 0"]
impl crate::Resettable for CLK_COUNTER_SPEC {}
