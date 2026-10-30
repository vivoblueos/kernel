#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster TIMERGROUP%s, containing TIMERGROUP?_CONF, TIMERGROUP?_TIMER_CLK_CONF, TIMERGROUP?_WDT_CLK_CONF"]
pub struct TIMERGROUP {
    conf: CONF,
    timer_clk_conf: TIMER_CLK_CONF,
    wdt_clk_conf: WDT_CLK_CONF,
}
impl TIMERGROUP {
    #[doc = "0x00 - TIMERGROUP0 configuration register"]
    #[inline(always)]
    pub const fn conf(&self) -> &CONF {
        &self.conf
    }
    #[doc = "0x04 - TIMERGROUP0_TIMER_CLK configuration register"]
    #[inline(always)]
    pub const fn timer_clk_conf(&self) -> &TIMER_CLK_CONF {
        &self.timer_clk_conf
    }
    #[doc = "0x08 - TIMERGROUP0_WDT_CLK configuration register"]
    #[inline(always)]
    pub const fn wdt_clk_conf(&self) -> &WDT_CLK_CONF {
        &self.wdt_clk_conf
    }
}
#[doc = "CONF (rw) register accessor: TIMERGROUP0 configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf`] module"]
pub type CONF = crate::Reg<conf::CONF_SPEC>;
#[doc = "TIMERGROUP0 configuration register"]
pub mod conf;
#[doc = "TIMER_CLK_CONF (rw) register accessor: TIMERGROUP0_TIMER_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`timer_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`timer_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@timer_clk_conf`] module"]
pub type TIMER_CLK_CONF = crate::Reg<timer_clk_conf::TIMER_CLK_CONF_SPEC>;
#[doc = "TIMERGROUP0_TIMER_CLK configuration register"]
pub mod timer_clk_conf;
#[doc = "WDT_CLK_CONF (rw) register accessor: TIMERGROUP0_WDT_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`wdt_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wdt_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wdt_clk_conf`] module"]
pub type WDT_CLK_CONF = crate::Reg<wdt_clk_conf::WDT_CLK_CONF_SPEC>;
#[doc = "TIMERGROUP0_WDT_CLK configuration register"]
pub mod wdt_clk_conf;
