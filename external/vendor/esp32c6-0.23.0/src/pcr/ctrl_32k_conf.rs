#[doc = "Register `CTRL_32K_CONF` reader"]
pub type R = crate::R<CTRL_32K_CONF_SPEC>;
#[doc = "Register `CTRL_32K_CONF` writer"]
pub type W = crate::W<CTRL_32K_CONF_SPEC>;
#[doc = "Field `CLK_32K_SEL` reader - This field indicates which one 32KHz clock will be used by MODEM_SYSTEM and timergroup. 0: OSC32K(default), 1: XTAL32K, 2/3: 32KHz from pad GPIO0."]
pub type CLK_32K_SEL_R = crate::FieldReader;
#[doc = "Field `CLK_32K_SEL` writer - This field indicates which one 32KHz clock will be used by MODEM_SYSTEM and timergroup. 0: OSC32K(default), 1: XTAL32K, 2/3: 32KHz from pad GPIO0."]
pub type CLK_32K_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - This field indicates which one 32KHz clock will be used by MODEM_SYSTEM and timergroup. 0: OSC32K(default), 1: XTAL32K, 2/3: 32KHz from pad GPIO0."]
    #[inline(always)]
    pub fn clk_32k_sel(&self) -> CLK_32K_SEL_R {
        CLK_32K_SEL_R::new((self.bits & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CTRL_32K_CONF")
            .field("clk_32k_sel", &self.clk_32k_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - This field indicates which one 32KHz clock will be used by MODEM_SYSTEM and timergroup. 0: OSC32K(default), 1: XTAL32K, 2/3: 32KHz from pad GPIO0."]
    #[inline(always)]
    pub fn clk_32k_sel(&mut self) -> CLK_32K_SEL_W<'_, CTRL_32K_CONF_SPEC> {
        CLK_32K_SEL_W::new(self, 0)
    }
}
#[doc = "32KHz clock configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl_32k_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl_32k_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CTRL_32K_CONF_SPEC;
impl crate::RegisterSpec for CTRL_32K_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctrl_32k_conf::R`](R) reader structure"]
impl crate::Readable for CTRL_32K_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ctrl_32k_conf::W`](W) writer structure"]
impl crate::Writable for CTRL_32K_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CTRL_32K_CONF to value 0"]
impl crate::Resettable for CTRL_32K_CONF_SPEC {}
