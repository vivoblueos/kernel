#[doc = "Register `MODEM_32K_CLK_CONF` reader"]
pub type R = crate::R<MODEM_32K_CLK_CONF_SPEC>;
#[doc = "Register `MODEM_32K_CLK_CONF` writer"]
pub type W = crate::W<MODEM_32K_CLK_CONF_SPEC>;
#[doc = "Field `CLK_MODEM_32K_SEL` reader - "]
pub type CLK_MODEM_32K_SEL_R = crate::FieldReader;
#[doc = "Field `CLK_MODEM_32K_SEL` writer - "]
pub type CLK_MODEM_32K_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1"]
    #[inline(always)]
    pub fn clk_modem_32k_sel(&self) -> CLK_MODEM_32K_SEL_R {
        CLK_MODEM_32K_SEL_R::new((self.bits & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MODEM_32K_CLK_CONF")
            .field("clk_modem_32k_sel", &self.clk_modem_32k_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1"]
    #[inline(always)]
    pub fn clk_modem_32k_sel(&mut self) -> CLK_MODEM_32K_SEL_W<'_, MODEM_32K_CLK_CONF_SPEC> {
        CLK_MODEM_32K_SEL_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`modem_32k_clk_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`modem_32k_clk_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MODEM_32K_CLK_CONF_SPEC;
impl crate::RegisterSpec for MODEM_32K_CLK_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`modem_32k_clk_conf::R`](R) reader structure"]
impl crate::Readable for MODEM_32K_CLK_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`modem_32k_clk_conf::W`](W) writer structure"]
impl crate::Writable for MODEM_32K_CLK_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MODEM_32K_CLK_CONF to value 0"]
impl crate::Resettable for MODEM_32K_CLK_CONF_SPEC {}
