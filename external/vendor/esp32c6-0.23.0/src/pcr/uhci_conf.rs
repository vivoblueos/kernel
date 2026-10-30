#[doc = "Register `UHCI_CONF` reader"]
pub type R = crate::R<UHCI_CONF_SPEC>;
#[doc = "Register `UHCI_CONF` writer"]
pub type W = crate::W<UHCI_CONF_SPEC>;
#[doc = "Field `UHCI_CLK_EN` reader - Set 1 to enable uhci clock"]
pub type UHCI_CLK_EN_R = crate::BitReader;
#[doc = "Field `UHCI_CLK_EN` writer - Set 1 to enable uhci clock"]
pub type UHCI_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UHCI_RST_EN` reader - Set 0 to reset uhci module"]
pub type UHCI_RST_EN_R = crate::BitReader;
#[doc = "Field `UHCI_RST_EN` writer - Set 0 to reset uhci module"]
pub type UHCI_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable uhci clock"]
    #[inline(always)]
    pub fn uhci_clk_en(&self) -> UHCI_CLK_EN_R {
        UHCI_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset uhci module"]
    #[inline(always)]
    pub fn uhci_rst_en(&self) -> UHCI_RST_EN_R {
        UHCI_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("UHCI_CONF")
            .field("uhci_clk_en", &self.uhci_clk_en())
            .field("uhci_rst_en", &self.uhci_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable uhci clock"]
    #[inline(always)]
    pub fn uhci_clk_en(&mut self) -> UHCI_CLK_EN_W<'_, UHCI_CONF_SPEC> {
        UHCI_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset uhci module"]
    #[inline(always)]
    pub fn uhci_rst_en(&mut self) -> UHCI_RST_EN_W<'_, UHCI_CONF_SPEC> {
        UHCI_RST_EN_W::new(self, 1)
    }
}
#[doc = "UHCI configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`uhci_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uhci_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct UHCI_CONF_SPEC;
impl crate::RegisterSpec for UHCI_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`uhci_conf::R`](R) reader structure"]
impl crate::Readable for UHCI_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`uhci_conf::W`](W) writer structure"]
impl crate::Writable for UHCI_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets UHCI_CONF to value 0x01"]
impl crate::Resettable for UHCI_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
