#[doc = "Register `MEM_MONITOR_CONF` reader"]
pub type R = crate::R<MEM_MONITOR_CONF_SPEC>;
#[doc = "Register `MEM_MONITOR_CONF` writer"]
pub type W = crate::W<MEM_MONITOR_CONF_SPEC>;
#[doc = "Field `MEM_MONITOR_CLK_EN` reader - Set 1 to enable mem_monitor clock"]
pub type MEM_MONITOR_CLK_EN_R = crate::BitReader;
#[doc = "Field `MEM_MONITOR_CLK_EN` writer - Set 1 to enable mem_monitor clock"]
pub type MEM_MONITOR_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MEM_MONITOR_RST_EN` reader - Set 0 to reset mem_monitor module"]
pub type MEM_MONITOR_RST_EN_R = crate::BitReader;
#[doc = "Field `MEM_MONITOR_RST_EN` writer - Set 0 to reset mem_monitor module"]
pub type MEM_MONITOR_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set 1 to enable mem_monitor clock"]
    #[inline(always)]
    pub fn mem_monitor_clk_en(&self) -> MEM_MONITOR_CLK_EN_R {
        MEM_MONITOR_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set 0 to reset mem_monitor module"]
    #[inline(always)]
    pub fn mem_monitor_rst_en(&self) -> MEM_MONITOR_RST_EN_R {
        MEM_MONITOR_RST_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MEM_MONITOR_CONF")
            .field("mem_monitor_clk_en", &self.mem_monitor_clk_en())
            .field("mem_monitor_rst_en", &self.mem_monitor_rst_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set 1 to enable mem_monitor clock"]
    #[inline(always)]
    pub fn mem_monitor_clk_en(&mut self) -> MEM_MONITOR_CLK_EN_W<'_, MEM_MONITOR_CONF_SPEC> {
        MEM_MONITOR_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set 0 to reset mem_monitor module"]
    #[inline(always)]
    pub fn mem_monitor_rst_en(&mut self) -> MEM_MONITOR_RST_EN_W<'_, MEM_MONITOR_CONF_SPEC> {
        MEM_MONITOR_RST_EN_W::new(self, 1)
    }
}
#[doc = "MEM_MONITOR configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_monitor_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_monitor_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MEM_MONITOR_CONF_SPEC;
impl crate::RegisterSpec for MEM_MONITOR_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mem_monitor_conf::R`](R) reader structure"]
impl crate::Readable for MEM_MONITOR_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mem_monitor_conf::W`](W) writer structure"]
impl crate::Writable for MEM_MONITOR_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MEM_MONITOR_CONF to value 0x01"]
impl crate::Resettable for MEM_MONITOR_CONF_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
