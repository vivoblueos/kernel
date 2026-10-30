#[doc = "Register `CLK_CONF_POWER_ST` reader"]
pub type R = crate::R<CLK_CONF_POWER_ST_SPEC>;
#[doc = "Register `CLK_CONF_POWER_ST` writer"]
pub type W = crate::W<CLK_CONF_POWER_ST_SPEC>;
#[doc = "Field `CLK_ZB_ST_MAP` reader - "]
pub type CLK_ZB_ST_MAP_R = crate::FieldReader;
#[doc = "Field `CLK_ZB_ST_MAP` writer - "]
pub type CLK_ZB_ST_MAP_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CLK_FE_ST_MAP` reader - "]
pub type CLK_FE_ST_MAP_R = crate::FieldReader;
#[doc = "Field `CLK_FE_ST_MAP` writer - "]
pub type CLK_FE_ST_MAP_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CLK_BT_ST_MAP` reader - "]
pub type CLK_BT_ST_MAP_R = crate::FieldReader;
#[doc = "Field `CLK_BT_ST_MAP` writer - "]
pub type CLK_BT_ST_MAP_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CLK_WIFI_ST_MAP` reader - "]
pub type CLK_WIFI_ST_MAP_R = crate::FieldReader;
#[doc = "Field `CLK_WIFI_ST_MAP` writer - "]
pub type CLK_WIFI_ST_MAP_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CLK_MODEM_PERI_ST_MAP` reader - "]
pub type CLK_MODEM_PERI_ST_MAP_R = crate::FieldReader;
#[doc = "Field `CLK_MODEM_PERI_ST_MAP` writer - "]
pub type CLK_MODEM_PERI_ST_MAP_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `CLK_MODEM_APB_ST_MAP` reader - "]
pub type CLK_MODEM_APB_ST_MAP_R = crate::FieldReader;
#[doc = "Field `CLK_MODEM_APB_ST_MAP` writer - "]
pub type CLK_MODEM_APB_ST_MAP_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 8:11"]
    #[inline(always)]
    pub fn clk_zb_st_map(&self) -> CLK_ZB_ST_MAP_R {
        CLK_ZB_ST_MAP_R::new(((self.bits >> 8) & 0x0f) as u8)
    }
    #[doc = "Bits 12:15"]
    #[inline(always)]
    pub fn clk_fe_st_map(&self) -> CLK_FE_ST_MAP_R {
        CLK_FE_ST_MAP_R::new(((self.bits >> 12) & 0x0f) as u8)
    }
    #[doc = "Bits 16:19"]
    #[inline(always)]
    pub fn clk_bt_st_map(&self) -> CLK_BT_ST_MAP_R {
        CLK_BT_ST_MAP_R::new(((self.bits >> 16) & 0x0f) as u8)
    }
    #[doc = "Bits 20:23"]
    #[inline(always)]
    pub fn clk_wifi_st_map(&self) -> CLK_WIFI_ST_MAP_R {
        CLK_WIFI_ST_MAP_R::new(((self.bits >> 20) & 0x0f) as u8)
    }
    #[doc = "Bits 24:27"]
    #[inline(always)]
    pub fn clk_modem_peri_st_map(&self) -> CLK_MODEM_PERI_ST_MAP_R {
        CLK_MODEM_PERI_ST_MAP_R::new(((self.bits >> 24) & 0x0f) as u8)
    }
    #[doc = "Bits 28:31"]
    #[inline(always)]
    pub fn clk_modem_apb_st_map(&self) -> CLK_MODEM_APB_ST_MAP_R {
        CLK_MODEM_APB_ST_MAP_R::new(((self.bits >> 28) & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLK_CONF_POWER_ST")
            .field("clk_zb_st_map", &self.clk_zb_st_map())
            .field("clk_fe_st_map", &self.clk_fe_st_map())
            .field("clk_bt_st_map", &self.clk_bt_st_map())
            .field("clk_wifi_st_map", &self.clk_wifi_st_map())
            .field("clk_modem_peri_st_map", &self.clk_modem_peri_st_map())
            .field("clk_modem_apb_st_map", &self.clk_modem_apb_st_map())
            .finish()
    }
}
impl W {
    #[doc = "Bits 8:11"]
    #[inline(always)]
    pub fn clk_zb_st_map(&mut self) -> CLK_ZB_ST_MAP_W<'_, CLK_CONF_POWER_ST_SPEC> {
        CLK_ZB_ST_MAP_W::new(self, 8)
    }
    #[doc = "Bits 12:15"]
    #[inline(always)]
    pub fn clk_fe_st_map(&mut self) -> CLK_FE_ST_MAP_W<'_, CLK_CONF_POWER_ST_SPEC> {
        CLK_FE_ST_MAP_W::new(self, 12)
    }
    #[doc = "Bits 16:19"]
    #[inline(always)]
    pub fn clk_bt_st_map(&mut self) -> CLK_BT_ST_MAP_W<'_, CLK_CONF_POWER_ST_SPEC> {
        CLK_BT_ST_MAP_W::new(self, 16)
    }
    #[doc = "Bits 20:23"]
    #[inline(always)]
    pub fn clk_wifi_st_map(&mut self) -> CLK_WIFI_ST_MAP_W<'_, CLK_CONF_POWER_ST_SPEC> {
        CLK_WIFI_ST_MAP_W::new(self, 20)
    }
    #[doc = "Bits 24:27"]
    #[inline(always)]
    pub fn clk_modem_peri_st_map(&mut self) -> CLK_MODEM_PERI_ST_MAP_W<'_, CLK_CONF_POWER_ST_SPEC> {
        CLK_MODEM_PERI_ST_MAP_W::new(self, 24)
    }
    #[doc = "Bits 28:31"]
    #[inline(always)]
    pub fn clk_modem_apb_st_map(&mut self) -> CLK_MODEM_APB_ST_MAP_W<'_, CLK_CONF_POWER_ST_SPEC> {
        CLK_MODEM_APB_ST_MAP_W::new(self, 28)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_conf_power_st::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_conf_power_st::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLK_CONF_POWER_ST_SPEC;
impl crate::RegisterSpec for CLK_CONF_POWER_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clk_conf_power_st::R`](R) reader structure"]
impl crate::Readable for CLK_CONF_POWER_ST_SPEC {}
#[doc = "`write(|w| ..)` method takes [`clk_conf_power_st::W`](W) writer structure"]
impl crate::Writable for CLK_CONF_POWER_ST_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CLK_CONF_POWER_ST to value 0"]
impl crate::Resettable for CLK_CONF_POWER_ST_SPEC {}
