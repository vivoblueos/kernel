#[doc = "Register `CLK_CFG` reader"]
pub type R = crate::R<CLK_CFG_SPEC>;
#[doc = "Register `CLK_CFG` writer"]
pub type W = crate::W<CLK_CFG_SPEC>;
#[doc = "Field `CLK_PRESCALE` reader - Period of PWM_clk = 6.25ns * (PWM_CLK_PRESCALE + 1)"]
pub type CLK_PRESCALE_R = crate::FieldReader;
#[doc = "Field `CLK_PRESCALE` writer - Period of PWM_clk = 6.25ns * (PWM_CLK_PRESCALE + 1)"]
pub type CLK_PRESCALE_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - Period of PWM_clk = 6.25ns * (PWM_CLK_PRESCALE + 1)"]
    #[inline(always)]
    pub fn clk_prescale(&self) -> CLK_PRESCALE_R {
        CLK_PRESCALE_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLK_CFG")
            .field("clk_prescale", &self.clk_prescale())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - Period of PWM_clk = 6.25ns * (PWM_CLK_PRESCALE + 1)"]
    #[inline(always)]
    pub fn clk_prescale(&mut self) -> CLK_PRESCALE_W<'_, CLK_CFG_SPEC> {
        CLK_PRESCALE_W::new(self, 0)
    }
}
#[doc = "PWM clock prescaler register.\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_cfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_cfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLK_CFG_SPEC;
impl crate::RegisterSpec for CLK_CFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clk_cfg::R`](R) reader structure"]
impl crate::Readable for CLK_CFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clk_cfg::W`](W) writer structure"]
impl crate::Writable for CLK_CFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLK_CFG to value 0"]
impl crate::Resettable for CLK_CFG_SPEC {}
