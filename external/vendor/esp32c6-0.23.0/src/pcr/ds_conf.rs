#[doc = "Register `DS_CONF` reader"]
pub type R = crate::R<DS_CONF_SPEC>;
#[doc = "Register `DS_CONF` writer"]
pub type W = crate::W<DS_CONF_SPEC>;
#[doc = "Field `DS_CLK_EN` reader - Set 1 to enable ds clock"]
pub type DS_CLK_EN_R = crate::BitReader;
#[doc = "Field `DS_CLK_EN` writer - Set 1 to enable ds clock"]
pub type DS_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DS_RST_EN` reader - Set 0 to reset ds module"]
pub type DS_RST_EN_R = crate::BitReader;
#[doc = "Field `DS_RST_EN` writer - Set 0 to reset ds module"]
pub type DS_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable ds clock"]
    #[inline(always)]
    pub fn ds_clk_en(&self) -> DS_CLK_EN_R {
        DS_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset ds module"]
    #[inline(always)]
    pub fn ds_rst_en(&self) -> DS_RST_EN_R {
        DS_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DS_CONF")
            .field("ds_clk_en", &self.ds_clk_en())
            .field("ds_rst_en", &self.ds_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable ds clock"]
    #[inline(always)]
    pub fn ds_clk_en(&mut self) -> DS_CLK_EN_W<'_, DS_CONF_SPEC> {
        DS_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset ds module"]
    #[inline(always)]
    pub fn ds_rst_en(&mut self) -> DS_RST_EN_W<'_, DS_CONF_SPEC> {
        DS_RST_EN_W::new(self, 1)
    }
}
#[doc = "DS configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ds_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ds_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DS_CONF_SPEC;
impl crate::RegisterSpec for DS_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ds_conf::R`](R) reader structure"]
impl crate::Readable for DS_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`ds_conf::W`](W) writer structure"]
impl crate::Writable for DS_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DS_CONF to value 0x01"]
impl crate::Resettable for DS_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
