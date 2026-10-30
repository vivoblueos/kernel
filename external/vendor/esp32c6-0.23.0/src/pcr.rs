#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    uart: [UART; 2],
    mspi_conf: MSPI_CONF,
    mspi_clk_conf: MSPI_CLK_CONF,
    i2c0_conf: I2C0_CONF,
    i2c_sclk_conf: I2C_SCLK_CONF,
    uhci_conf: UHCI_CONF,
    rmt_conf: RMT_CONF,
    rmt_sclk_conf: RMT_SCLK_CONF,
    ledc_conf: LEDC_CONF,
    ledc_sclk_conf: LEDC_SCLK_CONF,
    timergroup: [TIMERGROUP; 2],
    systimer_conf: SYSTIMER_CONF,
    systimer_func_clk_conf: SYSTIMER_FUNC_CLK_CONF,
    twai0_conf: TWAI0_CONF,
    twai0_func_clk_conf: TWAI0_FUNC_CLK_CONF,
    twai1_conf: TWAI1_CONF,
    twai1_func_clk_conf: TWAI1_FUNC_CLK_CONF,
    i2s_conf: I2S_CONF,
    i2s_tx_clkm_conf: I2S_TX_CLKM_CONF,
    i2s_tx_clkm_div_conf: I2S_TX_CLKM_DIV_CONF,
    i2s_rx_clkm_conf: I2S_RX_CLKM_CONF,
    i2s_rx_clkm_div_conf: I2S_RX_CLKM_DIV_CONF,
    saradc_conf: SARADC_CONF,
    saradc_clkm_conf: SARADC_CLKM_CONF,
    tsens_clk_conf: TSENS_CLK_CONF,
    usb_device_conf: USB_DEVICE_CONF,
    intmtx_conf: INTMTX_CONF,
    pcnt_conf: PCNT_CONF,
    etm_conf: ETM_CONF,
    pwm_conf: PWM_CONF,
    pwm_clk_conf: PWM_CLK_CONF,
    parl_io_conf: PARL_IO_CONF,
    parl_clk_rx_conf: PARL_CLK_RX_CONF,
    parl_clk_tx_conf: PARL_CLK_TX_CONF,
    sdio_slave_conf: SDIO_SLAVE_CONF,
    pvt_monitor_conf: PVT_MONITOR_CONF,
    pvt_monitor_func_clk_conf: PVT_MONITOR_FUNC_CLK_CONF,
    gdma_conf: GDMA_CONF,
    spi2_conf: SPI2_CONF,
    spi2_clkm_conf: SPI2_CLKM_CONF,
    aes_conf: AES_CONF,
    sha_conf: SHA_CONF,
    rsa_conf: RSA_CONF,
    rsa_pd_ctrl: RSA_PD_CTRL,
    ecc_conf: ECC_CONF,
    ecc_pd_ctrl: ECC_PD_CTRL,
    ds_conf: DS_CONF,
    hmac_conf: HMAC_CONF,
    iomux_conf: IOMUX_CONF,
    iomux_clk_conf: IOMUX_CLK_CONF,
    mem_monitor_conf: MEM_MONITOR_CONF,
    regdma_conf: REGDMA_CONF,
    retention_conf: RETENTION_CONF,
    trace_conf: TRACE_CONF,
    assist_conf: ASSIST_CONF,
    cache_conf: CACHE_CONF,
    modem_apb_conf: MODEM_APB_CONF,
    timeout_conf: TIMEOUT_CONF,
    sysclk_conf: SYSCLK_CONF,
    cpu_waiti_conf: CPU_WAITI_CONF,
    cpu_freq_conf: CPU_FREQ_CONF,
    ahb_freq_conf: AHB_FREQ_CONF,
    apb_freq_conf: APB_FREQ_CONF,
    sysclk_freq_query_0: SYSCLK_FREQ_QUERY_0,
    pll_div_clk_en: PLL_DIV_CLK_EN,
    ctrl_clk_out_en: CTRL_CLK_OUT_EN,
    ctrl_tick_conf: CTRL_TICK_CONF,
    ctrl_32k_conf: CTRL_32K_CONF,
    sram_power_conf: SRAM_POWER_CONF,
    _reserved69: [u8; 0x0eb4],
    reset_event_bypass: RESET_EVENT_BYPASS,
    fpga_debug: FPGA_DEBUG,
    clock_gate: CLOCK_GATE,
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00..0x18 - Cluster UART%s, containing UART?_CONF, UART?_SCLK_CONF, UART?_PD_CTRL"]
    #[inline(always)]
    pub const fn uart(&self, n: usize) -> &UART {
        &self.uart[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x00..0x18 - Cluster UART%s, containing UART?_CONF, UART?_SCLK_CONF, UART?_PD_CTRL"]
    #[inline(always)]
    pub fn uart_iter(&self) -> impl Iterator<Item = &UART> {
        self.uart.iter()
    }
    #[doc = "0x18 - MSPI configuration register"]
    #[inline(always)]
    pub const fn mspi_conf(&self) -> &MSPI_CONF {
        &self.mspi_conf
    }
    #[doc = "0x1c - MSPI_CLK configuration register"]
    #[inline(always)]
    pub const fn mspi_clk_conf(&self) -> &MSPI_CLK_CONF {
        &self.mspi_clk_conf
    }
    #[doc = "0x20 - I2C configuration register"]
    #[inline(always)]
    pub const fn i2c0_conf(&self) -> &I2C0_CONF {
        &self.i2c0_conf
    }
    #[doc = "0x24 - I2C_SCLK configuration register"]
    #[inline(always)]
    pub const fn i2c_sclk_conf(&self) -> &I2C_SCLK_CONF {
        &self.i2c_sclk_conf
    }
    #[doc = "0x28 - UHCI configuration register"]
    #[inline(always)]
    pub const fn uhci_conf(&self) -> &UHCI_CONF {
        &self.uhci_conf
    }
    #[doc = "0x2c - RMT configuration register"]
    #[inline(always)]
    pub const fn rmt_conf(&self) -> &RMT_CONF {
        &self.rmt_conf
    }
    #[doc = "0x30 - RMT_SCLK configuration register"]
    #[inline(always)]
    pub const fn rmt_sclk_conf(&self) -> &RMT_SCLK_CONF {
        &self.rmt_sclk_conf
    }
    #[doc = "0x34 - LEDC configuration register"]
    #[inline(always)]
    pub const fn ledc_conf(&self) -> &LEDC_CONF {
        &self.ledc_conf
    }
    #[doc = "0x38 - LEDC_SCLK configuration register"]
    #[inline(always)]
    pub const fn ledc_sclk_conf(&self) -> &LEDC_SCLK_CONF {
        &self.ledc_sclk_conf
    }
    #[doc = "0x3c..0x54 - Cluster TIMERGROUP%s, containing TIMERGROUP?_CONF, TIMERGROUP?_TIMER_CLK_CONF, TIMERGROUP?_WDT_CLK_CONF"]
    #[inline(always)]
    pub const fn timergroup(&self, n: usize) -> &TIMERGROUP {
        &self.timergroup[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x3c..0x54 - Cluster TIMERGROUP%s, containing TIMERGROUP?_CONF, TIMERGROUP?_TIMER_CLK_CONF, TIMERGROUP?_WDT_CLK_CONF"]
    #[inline(always)]
    pub fn timergroup_iter(&self) -> impl Iterator<Item = &TIMERGROUP> {
        self.timergroup.iter()
    }
    #[doc = "0x54 - SYSTIMER configuration register"]
    #[inline(always)]
    pub const fn systimer_conf(&self) -> &SYSTIMER_CONF {
        &self.systimer_conf
    }
    #[doc = "0x58 - SYSTIMER_FUNC_CLK configuration register"]
    #[inline(always)]
    pub const fn systimer_func_clk_conf(&self) -> &SYSTIMER_FUNC_CLK_CONF {
        &self.systimer_func_clk_conf
    }
    #[doc = "0x5c - TWAI0 configuration register"]
    #[inline(always)]
    pub const fn twai0_conf(&self) -> &TWAI0_CONF {
        &self.twai0_conf
    }
    #[doc = "0x60 - TWAI0_FUNC_CLK configuration register"]
    #[inline(always)]
    pub const fn twai0_func_clk_conf(&self) -> &TWAI0_FUNC_CLK_CONF {
        &self.twai0_func_clk_conf
    }
    #[doc = "0x64 - TWAI1 configuration register"]
    #[inline(always)]
    pub const fn twai1_conf(&self) -> &TWAI1_CONF {
        &self.twai1_conf
    }
    #[doc = "0x68 - TWAI1_FUNC_CLK configuration register"]
    #[inline(always)]
    pub const fn twai1_func_clk_conf(&self) -> &TWAI1_FUNC_CLK_CONF {
        &self.twai1_func_clk_conf
    }
    #[doc = "0x6c - I2S configuration register"]
    #[inline(always)]
    pub const fn i2s_conf(&self) -> &I2S_CONF {
        &self.i2s_conf
    }
    #[doc = "0x70 - I2S_TX_CLKM configuration register"]
    #[inline(always)]
    pub const fn i2s_tx_clkm_conf(&self) -> &I2S_TX_CLKM_CONF {
        &self.i2s_tx_clkm_conf
    }
    #[doc = "0x74 - I2S_TX_CLKM_DIV configuration register"]
    #[inline(always)]
    pub const fn i2s_tx_clkm_div_conf(&self) -> &I2S_TX_CLKM_DIV_CONF {
        &self.i2s_tx_clkm_div_conf
    }
    #[doc = "0x78 - I2S_RX_CLKM configuration register"]
    #[inline(always)]
    pub const fn i2s_rx_clkm_conf(&self) -> &I2S_RX_CLKM_CONF {
        &self.i2s_rx_clkm_conf
    }
    #[doc = "0x7c - I2S_RX_CLKM_DIV configuration register"]
    #[inline(always)]
    pub const fn i2s_rx_clkm_div_conf(&self) -> &I2S_RX_CLKM_DIV_CONF {
        &self.i2s_rx_clkm_div_conf
    }
    #[doc = "0x80 - SARADC configuration register"]
    #[inline(always)]
    pub const fn saradc_conf(&self) -> &SARADC_CONF {
        &self.saradc_conf
    }
    #[doc = "0x84 - SARADC_CLKM configuration register"]
    #[inline(always)]
    pub const fn saradc_clkm_conf(&self) -> &SARADC_CLKM_CONF {
        &self.saradc_clkm_conf
    }
    #[doc = "0x88 - TSENS_CLK configuration register"]
    #[inline(always)]
    pub const fn tsens_clk_conf(&self) -> &TSENS_CLK_CONF {
        &self.tsens_clk_conf
    }
    #[doc = "0x8c - USB_DEVICE configuration register"]
    #[inline(always)]
    pub const fn usb_device_conf(&self) -> &USB_DEVICE_CONF {
        &self.usb_device_conf
    }
    #[doc = "0x90 - INTMTX configuration register"]
    #[inline(always)]
    pub const fn intmtx_conf(&self) -> &INTMTX_CONF {
        &self.intmtx_conf
    }
    #[doc = "0x94 - PCNT configuration register"]
    #[inline(always)]
    pub const fn pcnt_conf(&self) -> &PCNT_CONF {
        &self.pcnt_conf
    }
    #[doc = "0x98 - ETM configuration register"]
    #[inline(always)]
    pub const fn etm_conf(&self) -> &ETM_CONF {
        &self.etm_conf
    }
    #[doc = "0x9c - PWM configuration register"]
    #[inline(always)]
    pub const fn pwm_conf(&self) -> &PWM_CONF {
        &self.pwm_conf
    }
    #[doc = "0xa0 - PWM_CLK configuration register"]
    #[inline(always)]
    pub const fn pwm_clk_conf(&self) -> &PWM_CLK_CONF {
        &self.pwm_clk_conf
    }
    #[doc = "0xa4 - PARL_IO configuration register"]
    #[inline(always)]
    pub const fn parl_io_conf(&self) -> &PARL_IO_CONF {
        &self.parl_io_conf
    }
    #[doc = "0xa8 - PARL_CLK_RX configuration register"]
    #[inline(always)]
    pub const fn parl_clk_rx_conf(&self) -> &PARL_CLK_RX_CONF {
        &self.parl_clk_rx_conf
    }
    #[doc = "0xac - PARL_CLK_TX configuration register"]
    #[inline(always)]
    pub const fn parl_clk_tx_conf(&self) -> &PARL_CLK_TX_CONF {
        &self.parl_clk_tx_conf
    }
    #[doc = "0xb0 - SDIO_SLAVE configuration register"]
    #[inline(always)]
    pub const fn sdio_slave_conf(&self) -> &SDIO_SLAVE_CONF {
        &self.sdio_slave_conf
    }
    #[doc = "0xb4 - PVT_MONITOR configuration register"]
    #[inline(always)]
    pub const fn pvt_monitor_conf(&self) -> &PVT_MONITOR_CONF {
        &self.pvt_monitor_conf
    }
    #[doc = "0xb8 - PVT_MONITOR function clock configuration register"]
    #[inline(always)]
    pub const fn pvt_monitor_func_clk_conf(&self) -> &PVT_MONITOR_FUNC_CLK_CONF {
        &self.pvt_monitor_func_clk_conf
    }
    #[doc = "0xbc - GDMA configuration register"]
    #[inline(always)]
    pub const fn gdma_conf(&self) -> &GDMA_CONF {
        &self.gdma_conf
    }
    #[doc = "0xc0 - SPI2 configuration register"]
    #[inline(always)]
    pub const fn spi2_conf(&self) -> &SPI2_CONF {
        &self.spi2_conf
    }
    #[doc = "0xc4 - SPI2_CLKM configuration register"]
    #[inline(always)]
    pub const fn spi2_clkm_conf(&self) -> &SPI2_CLKM_CONF {
        &self.spi2_clkm_conf
    }
    #[doc = "0xc8 - AES configuration register"]
    #[inline(always)]
    pub const fn aes_conf(&self) -> &AES_CONF {
        &self.aes_conf
    }
    #[doc = "0xcc - SHA configuration register"]
    #[inline(always)]
    pub const fn sha_conf(&self) -> &SHA_CONF {
        &self.sha_conf
    }
    #[doc = "0xd0 - RSA configuration register"]
    #[inline(always)]
    pub const fn rsa_conf(&self) -> &RSA_CONF {
        &self.rsa_conf
    }
    #[doc = "0xd4 - RSA power control register"]
    #[inline(always)]
    pub const fn rsa_pd_ctrl(&self) -> &RSA_PD_CTRL {
        &self.rsa_pd_ctrl
    }
    #[doc = "0xd8 - ECC configuration register"]
    #[inline(always)]
    pub const fn ecc_conf(&self) -> &ECC_CONF {
        &self.ecc_conf
    }
    #[doc = "0xdc - ECC power control register"]
    #[inline(always)]
    pub const fn ecc_pd_ctrl(&self) -> &ECC_PD_CTRL {
        &self.ecc_pd_ctrl
    }
    #[doc = "0xe0 - DS configuration register"]
    #[inline(always)]
    pub const fn ds_conf(&self) -> &DS_CONF {
        &self.ds_conf
    }
    #[doc = "0xe4 - HMAC configuration register"]
    #[inline(always)]
    pub const fn hmac_conf(&self) -> &HMAC_CONF {
        &self.hmac_conf
    }
    #[doc = "0xe8 - IOMUX configuration register"]
    #[inline(always)]
    pub const fn iomux_conf(&self) -> &IOMUX_CONF {
        &self.iomux_conf
    }
    #[doc = "0xec - IOMUX_CLK configuration register"]
    #[inline(always)]
    pub const fn iomux_clk_conf(&self) -> &IOMUX_CLK_CONF {
        &self.iomux_clk_conf
    }
    #[doc = "0xf0 - MEM_MONITOR configuration register"]
    #[inline(always)]
    pub const fn mem_monitor_conf(&self) -> &MEM_MONITOR_CONF {
        &self.mem_monitor_conf
    }
    #[doc = "0xf4 - REGDMA configuration register"]
    #[inline(always)]
    pub const fn regdma_conf(&self) -> &REGDMA_CONF {
        &self.regdma_conf
    }
    #[doc = "0xf8 - retention configuration register"]
    #[inline(always)]
    pub const fn retention_conf(&self) -> &RETENTION_CONF {
        &self.retention_conf
    }
    #[doc = "0xfc - TRACE configuration register"]
    #[inline(always)]
    pub const fn trace_conf(&self) -> &TRACE_CONF {
        &self.trace_conf
    }
    #[doc = "0x100 - ASSIST configuration register"]
    #[inline(always)]
    pub const fn assist_conf(&self) -> &ASSIST_CONF {
        &self.assist_conf
    }
    #[doc = "0x104 - CACHE configuration register"]
    #[inline(always)]
    pub const fn cache_conf(&self) -> &CACHE_CONF {
        &self.cache_conf
    }
    #[doc = "0x108 - MODEM_APB configuration register"]
    #[inline(always)]
    pub const fn modem_apb_conf(&self) -> &MODEM_APB_CONF {
        &self.modem_apb_conf
    }
    #[doc = "0x10c - TIMEOUT configuration register"]
    #[inline(always)]
    pub const fn timeout_conf(&self) -> &TIMEOUT_CONF {
        &self.timeout_conf
    }
    #[doc = "0x110 - SYSCLK configuration register"]
    #[inline(always)]
    pub const fn sysclk_conf(&self) -> &SYSCLK_CONF {
        &self.sysclk_conf
    }
    #[doc = "0x114 - CPU_WAITI configuration register"]
    #[inline(always)]
    pub const fn cpu_waiti_conf(&self) -> &CPU_WAITI_CONF {
        &self.cpu_waiti_conf
    }
    #[doc = "0x118 - CPU_FREQ configuration register"]
    #[inline(always)]
    pub const fn cpu_freq_conf(&self) -> &CPU_FREQ_CONF {
        &self.cpu_freq_conf
    }
    #[doc = "0x11c - AHB_FREQ configuration register"]
    #[inline(always)]
    pub const fn ahb_freq_conf(&self) -> &AHB_FREQ_CONF {
        &self.ahb_freq_conf
    }
    #[doc = "0x120 - APB_FREQ configuration register"]
    #[inline(always)]
    pub const fn apb_freq_conf(&self) -> &APB_FREQ_CONF {
        &self.apb_freq_conf
    }
    #[doc = "0x124 - SYSCLK frequency query 0 register"]
    #[inline(always)]
    pub const fn sysclk_freq_query_0(&self) -> &SYSCLK_FREQ_QUERY_0 {
        &self.sysclk_freq_query_0
    }
    #[doc = "0x128 - SPLL DIV clock-gating configuration register"]
    #[inline(always)]
    pub const fn pll_div_clk_en(&self) -> &PLL_DIV_CLK_EN {
        &self.pll_div_clk_en
    }
    #[doc = "0x12c - CLK_OUT_EN configuration register"]
    #[inline(always)]
    pub const fn ctrl_clk_out_en(&self) -> &CTRL_CLK_OUT_EN {
        &self.ctrl_clk_out_en
    }
    #[doc = "0x130 - TICK configuration register"]
    #[inline(always)]
    pub const fn ctrl_tick_conf(&self) -> &CTRL_TICK_CONF {
        &self.ctrl_tick_conf
    }
    #[doc = "0x134 - 32KHz clock configuration register"]
    #[inline(always)]
    pub const fn ctrl_32k_conf(&self) -> &CTRL_32K_CONF {
        &self.ctrl_32k_conf
    }
    #[doc = "0x138 - HP SRAM/ROM configuration register"]
    #[inline(always)]
    pub const fn sram_power_conf(&self) -> &SRAM_POWER_CONF {
        &self.sram_power_conf
    }
    #[doc = "0xff0 - reset event bypass backdoor configuration register"]
    #[inline(always)]
    pub const fn reset_event_bypass(&self) -> &RESET_EVENT_BYPASS {
        &self.reset_event_bypass
    }
    #[doc = "0xff4 - fpga debug register"]
    #[inline(always)]
    pub const fn fpga_debug(&self) -> &FPGA_DEBUG {
        &self.fpga_debug
    }
    #[doc = "0xff8 - PCR clock gating configure register"]
    #[inline(always)]
    pub const fn clock_gate(&self) -> &CLOCK_GATE {
        &self.clock_gate
    }
    #[doc = "0xffc - Date register."]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "Cluster UART%s, containing UART?_CONF, UART?_SCLK_CONF, UART?_PD_CTRL"]
pub use self::uart::UART;
#[doc = r"Cluster"]
#[doc = "Cluster UART%s, containing UART?_CONF, UART?_SCLK_CONF, UART?_PD_CTRL"]
pub mod uart;
#[doc = "MSPI_CONF (rw) register accessor: MSPI configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`mspi_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mspi_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mspi_conf`] module"]
pub type MSPI_CONF = crate::Reg<mspi_conf::MSPI_CONF_SPEC>;
#[doc = "MSPI configuration register"]
pub mod mspi_conf;
#[doc = "MSPI_CLK_CONF (rw) register accessor: MSPI_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`mspi_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mspi_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mspi_clk_conf`] module"]
pub type MSPI_CLK_CONF = crate::Reg<mspi_clk_conf::MSPI_CLK_CONF_SPEC>;
#[doc = "MSPI_CLK configuration register"]
pub mod mspi_clk_conf;
#[doc = "I2C0_CONF (rw) register accessor: I2C configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c0_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c0_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2c0_conf`] module"]
pub type I2C0_CONF = crate::Reg<i2c0_conf::I2C0_CONF_SPEC>;
#[doc = "I2C configuration register"]
pub mod i2c0_conf;
#[doc = "I2C_SCLK_CONF (rw) register accessor: I2C_SCLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c_sclk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c_sclk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2c_sclk_conf`] module"]
pub type I2C_SCLK_CONF = crate::Reg<i2c_sclk_conf::I2C_SCLK_CONF_SPEC>;
#[doc = "I2C_SCLK configuration register"]
pub mod i2c_sclk_conf;
#[doc = "UHCI_CONF (rw) register accessor: UHCI configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`uhci_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`uhci_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@uhci_conf`] module"]
pub type UHCI_CONF = crate::Reg<uhci_conf::UHCI_CONF_SPEC>;
#[doc = "UHCI configuration register"]
pub mod uhci_conf;
#[doc = "RMT_CONF (rw) register accessor: RMT configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`rmt_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rmt_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rmt_conf`] module"]
pub type RMT_CONF = crate::Reg<rmt_conf::RMT_CONF_SPEC>;
#[doc = "RMT configuration register"]
pub mod rmt_conf;
#[doc = "RMT_SCLK_CONF (rw) register accessor: RMT_SCLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`rmt_sclk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rmt_sclk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rmt_sclk_conf`] module"]
pub type RMT_SCLK_CONF = crate::Reg<rmt_sclk_conf::RMT_SCLK_CONF_SPEC>;
#[doc = "RMT_SCLK configuration register"]
pub mod rmt_sclk_conf;
#[doc = "LEDC_CONF (rw) register accessor: LEDC configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ledc_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ledc_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ledc_conf`] module"]
pub type LEDC_CONF = crate::Reg<ledc_conf::LEDC_CONF_SPEC>;
#[doc = "LEDC configuration register"]
pub mod ledc_conf;
#[doc = "LEDC_SCLK_CONF (rw) register accessor: LEDC_SCLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ledc_sclk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ledc_sclk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ledc_sclk_conf`] module"]
pub type LEDC_SCLK_CONF = crate::Reg<ledc_sclk_conf::LEDC_SCLK_CONF_SPEC>;
#[doc = "LEDC_SCLK configuration register"]
pub mod ledc_sclk_conf;
#[doc = "Cluster TIMERGROUP%s, containing TIMERGROUP?_CONF, TIMERGROUP?_TIMER_CLK_CONF, TIMERGROUP?_WDT_CLK_CONF"]
pub use self::timergroup::TIMERGROUP;
#[doc = r"Cluster"]
#[doc = "Cluster TIMERGROUP%s, containing TIMERGROUP?_CONF, TIMERGROUP?_TIMER_CLK_CONF, TIMERGROUP?_WDT_CLK_CONF"]
pub mod timergroup;
#[doc = "SYSTIMER_CONF (rw) register accessor: SYSTIMER configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`systimer_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`systimer_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@systimer_conf`] module"]
pub type SYSTIMER_CONF = crate::Reg<systimer_conf::SYSTIMER_CONF_SPEC>;
#[doc = "SYSTIMER configuration register"]
pub mod systimer_conf;
#[doc = "SYSTIMER_FUNC_CLK_CONF (rw) register accessor: SYSTIMER_FUNC_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`systimer_func_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`systimer_func_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@systimer_func_clk_conf`] module"]
pub type SYSTIMER_FUNC_CLK_CONF = crate::Reg<systimer_func_clk_conf::SYSTIMER_FUNC_CLK_CONF_SPEC>;
#[doc = "SYSTIMER_FUNC_CLK configuration register"]
pub mod systimer_func_clk_conf;
#[doc = "TWAI0_CONF (rw) register accessor: TWAI0 configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`twai0_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`twai0_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@twai0_conf`] module"]
pub type TWAI0_CONF = crate::Reg<twai0_conf::TWAI0_CONF_SPEC>;
#[doc = "TWAI0 configuration register"]
pub mod twai0_conf;
#[doc = "TWAI0_FUNC_CLK_CONF (rw) register accessor: TWAI0_FUNC_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`twai0_func_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`twai0_func_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@twai0_func_clk_conf`] module"]
pub type TWAI0_FUNC_CLK_CONF = crate::Reg<twai0_func_clk_conf::TWAI0_FUNC_CLK_CONF_SPEC>;
#[doc = "TWAI0_FUNC_CLK configuration register"]
pub mod twai0_func_clk_conf;
#[doc = "TWAI1_CONF (rw) register accessor: TWAI1 configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`twai1_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`twai1_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@twai1_conf`] module"]
pub type TWAI1_CONF = crate::Reg<twai1_conf::TWAI1_CONF_SPEC>;
#[doc = "TWAI1 configuration register"]
pub mod twai1_conf;
#[doc = "TWAI1_FUNC_CLK_CONF (rw) register accessor: TWAI1_FUNC_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`twai1_func_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`twai1_func_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@twai1_func_clk_conf`] module"]
pub type TWAI1_FUNC_CLK_CONF = crate::Reg<twai1_func_clk_conf::TWAI1_FUNC_CLK_CONF_SPEC>;
#[doc = "TWAI1_FUNC_CLK configuration register"]
pub mod twai1_func_clk_conf;
#[doc = "I2S_CONF (rw) register accessor: I2S configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2s_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2s_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2s_conf`] module"]
pub type I2S_CONF = crate::Reg<i2s_conf::I2S_CONF_SPEC>;
#[doc = "I2S configuration register"]
pub mod i2s_conf;
#[doc = "I2S_TX_CLKM_CONF (rw) register accessor: I2S_TX_CLKM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2s_tx_clkm_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2s_tx_clkm_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2s_tx_clkm_conf`] module"]
pub type I2S_TX_CLKM_CONF = crate::Reg<i2s_tx_clkm_conf::I2S_TX_CLKM_CONF_SPEC>;
#[doc = "I2S_TX_CLKM configuration register"]
pub mod i2s_tx_clkm_conf;
#[doc = "I2S_TX_CLKM_DIV_CONF (rw) register accessor: I2S_TX_CLKM_DIV configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2s_tx_clkm_div_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2s_tx_clkm_div_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2s_tx_clkm_div_conf`] module"]
pub type I2S_TX_CLKM_DIV_CONF = crate::Reg<i2s_tx_clkm_div_conf::I2S_TX_CLKM_DIV_CONF_SPEC>;
#[doc = "I2S_TX_CLKM_DIV configuration register"]
pub mod i2s_tx_clkm_div_conf;
#[doc = "I2S_RX_CLKM_CONF (rw) register accessor: I2S_RX_CLKM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2s_rx_clkm_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2s_rx_clkm_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2s_rx_clkm_conf`] module"]
pub type I2S_RX_CLKM_CONF = crate::Reg<i2s_rx_clkm_conf::I2S_RX_CLKM_CONF_SPEC>;
#[doc = "I2S_RX_CLKM configuration register"]
pub mod i2s_rx_clkm_conf;
#[doc = "I2S_RX_CLKM_DIV_CONF (rw) register accessor: I2S_RX_CLKM_DIV configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2s_rx_clkm_div_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2s_rx_clkm_div_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2s_rx_clkm_div_conf`] module"]
pub type I2S_RX_CLKM_DIV_CONF = crate::Reg<i2s_rx_clkm_div_conf::I2S_RX_CLKM_DIV_CONF_SPEC>;
#[doc = "I2S_RX_CLKM_DIV configuration register"]
pub mod i2s_rx_clkm_div_conf;
#[doc = "SARADC_CONF (rw) register accessor: SARADC configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`saradc_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`saradc_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@saradc_conf`] module"]
pub type SARADC_CONF = crate::Reg<saradc_conf::SARADC_CONF_SPEC>;
#[doc = "SARADC configuration register"]
pub mod saradc_conf;
#[doc = "SARADC_CLKM_CONF (rw) register accessor: SARADC_CLKM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`saradc_clkm_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`saradc_clkm_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@saradc_clkm_conf`] module"]
pub type SARADC_CLKM_CONF = crate::Reg<saradc_clkm_conf::SARADC_CLKM_CONF_SPEC>;
#[doc = "SARADC_CLKM configuration register"]
pub mod saradc_clkm_conf;
#[doc = "TSENS_CLK_CONF (rw) register accessor: TSENS_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`tsens_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tsens_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tsens_clk_conf`] module"]
pub type TSENS_CLK_CONF = crate::Reg<tsens_clk_conf::TSENS_CLK_CONF_SPEC>;
#[doc = "TSENS_CLK configuration register"]
pub mod tsens_clk_conf;
#[doc = "USB_DEVICE_CONF (rw) register accessor: USB_DEVICE configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`usb_device_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`usb_device_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@usb_device_conf`] module"]
pub type USB_DEVICE_CONF = crate::Reg<usb_device_conf::USB_DEVICE_CONF_SPEC>;
#[doc = "USB_DEVICE configuration register"]
pub mod usb_device_conf;
#[doc = "INTMTX_CONF (rw) register accessor: INTMTX configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`intmtx_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`intmtx_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@intmtx_conf`] module"]
pub type INTMTX_CONF = crate::Reg<intmtx_conf::INTMTX_CONF_SPEC>;
#[doc = "INTMTX configuration register"]
pub mod intmtx_conf;
#[doc = "PCNT_CONF (rw) register accessor: PCNT configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`pcnt_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pcnt_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pcnt_conf`] module"]
pub type PCNT_CONF = crate::Reg<pcnt_conf::PCNT_CONF_SPEC>;
#[doc = "PCNT configuration register"]
pub mod pcnt_conf;
#[doc = "ETM_CONF (rw) register accessor: ETM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`etm_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`etm_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@etm_conf`] module"]
pub type ETM_CONF = crate::Reg<etm_conf::ETM_CONF_SPEC>;
#[doc = "ETM configuration register"]
pub mod etm_conf;
#[doc = "PWM_CONF (rw) register accessor: PWM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`pwm_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pwm_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pwm_conf`] module"]
pub type PWM_CONF = crate::Reg<pwm_conf::PWM_CONF_SPEC>;
#[doc = "PWM configuration register"]
pub mod pwm_conf;
#[doc = "PWM_CLK_CONF (rw) register accessor: PWM_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`pwm_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pwm_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pwm_clk_conf`] module"]
pub type PWM_CLK_CONF = crate::Reg<pwm_clk_conf::PWM_CLK_CONF_SPEC>;
#[doc = "PWM_CLK configuration register"]
pub mod pwm_clk_conf;
#[doc = "PARL_IO_CONF (rw) register accessor: PARL_IO configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`parl_io_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`parl_io_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@parl_io_conf`] module"]
pub type PARL_IO_CONF = crate::Reg<parl_io_conf::PARL_IO_CONF_SPEC>;
#[doc = "PARL_IO configuration register"]
pub mod parl_io_conf;
#[doc = "PARL_CLK_RX_CONF (rw) register accessor: PARL_CLK_RX configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`parl_clk_rx_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`parl_clk_rx_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@parl_clk_rx_conf`] module"]
pub type PARL_CLK_RX_CONF = crate::Reg<parl_clk_rx_conf::PARL_CLK_RX_CONF_SPEC>;
#[doc = "PARL_CLK_RX configuration register"]
pub mod parl_clk_rx_conf;
#[doc = "PARL_CLK_TX_CONF (rw) register accessor: PARL_CLK_TX configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`parl_clk_tx_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`parl_clk_tx_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@parl_clk_tx_conf`] module"]
pub type PARL_CLK_TX_CONF = crate::Reg<parl_clk_tx_conf::PARL_CLK_TX_CONF_SPEC>;
#[doc = "PARL_CLK_TX configuration register"]
pub mod parl_clk_tx_conf;
#[doc = "SDIO_SLAVE_CONF (rw) register accessor: SDIO_SLAVE configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sdio_slave_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sdio_slave_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sdio_slave_conf`] module"]
pub type SDIO_SLAVE_CONF = crate::Reg<sdio_slave_conf::SDIO_SLAVE_CONF_SPEC>;
#[doc = "SDIO_SLAVE configuration register"]
pub mod sdio_slave_conf;
#[doc = "PVT_MONITOR_CONF (rw) register accessor: PVT_MONITOR configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`pvt_monitor_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pvt_monitor_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pvt_monitor_conf`] module"]
pub type PVT_MONITOR_CONF = crate::Reg<pvt_monitor_conf::PVT_MONITOR_CONF_SPEC>;
#[doc = "PVT_MONITOR configuration register"]
pub mod pvt_monitor_conf;
#[doc = "PVT_MONITOR_FUNC_CLK_CONF (rw) register accessor: PVT_MONITOR function clock configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`pvt_monitor_func_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pvt_monitor_func_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pvt_monitor_func_clk_conf`] module"]
pub type PVT_MONITOR_FUNC_CLK_CONF =
    crate::Reg<pvt_monitor_func_clk_conf::PVT_MONITOR_FUNC_CLK_CONF_SPEC>;
#[doc = "PVT_MONITOR function clock configuration register"]
pub mod pvt_monitor_func_clk_conf;
#[doc = "GDMA_CONF (rw) register accessor: GDMA configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`gdma_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`gdma_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gdma_conf`] module"]
pub type GDMA_CONF = crate::Reg<gdma_conf::GDMA_CONF_SPEC>;
#[doc = "GDMA configuration register"]
pub mod gdma_conf;
#[doc = "SPI2_CONF (rw) register accessor: SPI2 configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`spi2_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`spi2_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@spi2_conf`] module"]
pub type SPI2_CONF = crate::Reg<spi2_conf::SPI2_CONF_SPEC>;
#[doc = "SPI2 configuration register"]
pub mod spi2_conf;
#[doc = "SPI2_CLKM_CONF (rw) register accessor: SPI2_CLKM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`spi2_clkm_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`spi2_clkm_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@spi2_clkm_conf`] module"]
pub type SPI2_CLKM_CONF = crate::Reg<spi2_clkm_conf::SPI2_CLKM_CONF_SPEC>;
#[doc = "SPI2_CLKM configuration register"]
pub mod spi2_clkm_conf;
#[doc = "AES_CONF (rw) register accessor: AES configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`aes_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`aes_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@aes_conf`] module"]
pub type AES_CONF = crate::Reg<aes_conf::AES_CONF_SPEC>;
#[doc = "AES configuration register"]
pub mod aes_conf;
#[doc = "SHA_CONF (rw) register accessor: SHA configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sha_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sha_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sha_conf`] module"]
pub type SHA_CONF = crate::Reg<sha_conf::SHA_CONF_SPEC>;
#[doc = "SHA configuration register"]
pub mod sha_conf;
#[doc = "RSA_CONF (rw) register accessor: RSA configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`rsa_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rsa_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rsa_conf`] module"]
pub type RSA_CONF = crate::Reg<rsa_conf::RSA_CONF_SPEC>;
#[doc = "RSA configuration register"]
pub mod rsa_conf;
#[doc = "RSA_PD_CTRL (rw) register accessor: RSA power control register\n\nYou can [`read`](crate::Reg::read) this register and get [`rsa_pd_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rsa_pd_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rsa_pd_ctrl`] module"]
pub type RSA_PD_CTRL = crate::Reg<rsa_pd_ctrl::RSA_PD_CTRL_SPEC>;
#[doc = "RSA power control register"]
pub mod rsa_pd_ctrl;
#[doc = "ECC_CONF (rw) register accessor: ECC configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ecc_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ecc_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ecc_conf`] module"]
pub type ECC_CONF = crate::Reg<ecc_conf::ECC_CONF_SPEC>;
#[doc = "ECC configuration register"]
pub mod ecc_conf;
#[doc = "ECC_PD_CTRL (rw) register accessor: ECC power control register\n\nYou can [`read`](crate::Reg::read) this register and get [`ecc_pd_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ecc_pd_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ecc_pd_ctrl`] module"]
pub type ECC_PD_CTRL = crate::Reg<ecc_pd_ctrl::ECC_PD_CTRL_SPEC>;
#[doc = "ECC power control register"]
pub mod ecc_pd_ctrl;
#[doc = "DS_CONF (rw) register accessor: DS configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ds_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ds_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ds_conf`] module"]
pub type DS_CONF = crate::Reg<ds_conf::DS_CONF_SPEC>;
#[doc = "DS configuration register"]
pub mod ds_conf;
#[doc = "HMAC_CONF (rw) register accessor: HMAC configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`hmac_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hmac_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hmac_conf`] module"]
pub type HMAC_CONF = crate::Reg<hmac_conf::HMAC_CONF_SPEC>;
#[doc = "HMAC configuration register"]
pub mod hmac_conf;
#[doc = "IOMUX_CONF (rw) register accessor: IOMUX configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`iomux_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`iomux_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@iomux_conf`] module"]
pub type IOMUX_CONF = crate::Reg<iomux_conf::IOMUX_CONF_SPEC>;
#[doc = "IOMUX configuration register"]
pub mod iomux_conf;
#[doc = "IOMUX_CLK_CONF (rw) register accessor: IOMUX_CLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`iomux_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`iomux_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@iomux_clk_conf`] module"]
pub type IOMUX_CLK_CONF = crate::Reg<iomux_clk_conf::IOMUX_CLK_CONF_SPEC>;
#[doc = "IOMUX_CLK configuration register"]
pub mod iomux_clk_conf;
#[doc = "MEM_MONITOR_CONF (rw) register accessor: MEM_MONITOR configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_monitor_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_monitor_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mem_monitor_conf`] module"]
pub type MEM_MONITOR_CONF = crate::Reg<mem_monitor_conf::MEM_MONITOR_CONF_SPEC>;
#[doc = "MEM_MONITOR configuration register"]
pub mod mem_monitor_conf;
#[doc = "REGDMA_CONF (rw) register accessor: REGDMA configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`regdma_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`regdma_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@regdma_conf`] module"]
pub type REGDMA_CONF = crate::Reg<regdma_conf::REGDMA_CONF_SPEC>;
#[doc = "REGDMA configuration register"]
pub mod regdma_conf;
#[doc = "RETENTION_CONF (rw) register accessor: retention configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`retention_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`retention_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@retention_conf`] module"]
pub type RETENTION_CONF = crate::Reg<retention_conf::RETENTION_CONF_SPEC>;
#[doc = "retention configuration register"]
pub mod retention_conf;
#[doc = "TRACE_CONF (rw) register accessor: TRACE configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`trace_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`trace_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@trace_conf`] module"]
pub type TRACE_CONF = crate::Reg<trace_conf::TRACE_CONF_SPEC>;
#[doc = "TRACE configuration register"]
pub mod trace_conf;
#[doc = "ASSIST_CONF (rw) register accessor: ASSIST configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`assist_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`assist_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@assist_conf`] module"]
pub type ASSIST_CONF = crate::Reg<assist_conf::ASSIST_CONF_SPEC>;
#[doc = "ASSIST configuration register"]
pub mod assist_conf;
#[doc = "CACHE_CONF (rw) register accessor: CACHE configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cache_conf`] module"]
pub type CACHE_CONF = crate::Reg<cache_conf::CACHE_CONF_SPEC>;
#[doc = "CACHE configuration register"]
pub mod cache_conf;
#[doc = "MODEM_APB_CONF (rw) register accessor: MODEM_APB configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`modem_apb_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`modem_apb_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@modem_apb_conf`] module"]
pub type MODEM_APB_CONF = crate::Reg<modem_apb_conf::MODEM_APB_CONF_SPEC>;
#[doc = "MODEM_APB configuration register"]
pub mod modem_apb_conf;
#[doc = "TIMEOUT_CONF (rw) register accessor: TIMEOUT configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`timeout_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`timeout_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@timeout_conf`] module"]
pub type TIMEOUT_CONF = crate::Reg<timeout_conf::TIMEOUT_CONF_SPEC>;
#[doc = "TIMEOUT configuration register"]
pub mod timeout_conf;
#[doc = "SYSCLK_CONF (rw) register accessor: SYSCLK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sysclk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sysclk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sysclk_conf`] module"]
pub type SYSCLK_CONF = crate::Reg<sysclk_conf::SYSCLK_CONF_SPEC>;
#[doc = "SYSCLK configuration register"]
pub mod sysclk_conf;
#[doc = "CPU_WAITI_CONF (rw) register accessor: CPU_WAITI configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_waiti_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_waiti_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_waiti_conf`] module"]
pub type CPU_WAITI_CONF = crate::Reg<cpu_waiti_conf::CPU_WAITI_CONF_SPEC>;
#[doc = "CPU_WAITI configuration register"]
pub mod cpu_waiti_conf;
#[doc = "CPU_FREQ_CONF (rw) register accessor: CPU_FREQ configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`cpu_freq_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cpu_freq_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cpu_freq_conf`] module"]
pub type CPU_FREQ_CONF = crate::Reg<cpu_freq_conf::CPU_FREQ_CONF_SPEC>;
#[doc = "CPU_FREQ configuration register"]
pub mod cpu_freq_conf;
#[doc = "AHB_FREQ_CONF (rw) register accessor: AHB_FREQ configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ahb_freq_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ahb_freq_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ahb_freq_conf`] module"]
pub type AHB_FREQ_CONF = crate::Reg<ahb_freq_conf::AHB_FREQ_CONF_SPEC>;
#[doc = "AHB_FREQ configuration register"]
pub mod ahb_freq_conf;
#[doc = "APB_FREQ_CONF (rw) register accessor: APB_FREQ configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`apb_freq_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`apb_freq_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@apb_freq_conf`] module"]
pub type APB_FREQ_CONF = crate::Reg<apb_freq_conf::APB_FREQ_CONF_SPEC>;
#[doc = "APB_FREQ configuration register"]
pub mod apb_freq_conf;
#[doc = "SYSCLK_FREQ_QUERY_0 (r) register accessor: SYSCLK frequency query 0 register\n\nYou can [`read`](crate::Reg::read) this register and get [`sysclk_freq_query_0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sysclk_freq_query_0`] module"]
pub type SYSCLK_FREQ_QUERY_0 = crate::Reg<sysclk_freq_query_0::SYSCLK_FREQ_QUERY_0_SPEC>;
#[doc = "SYSCLK frequency query 0 register"]
pub mod sysclk_freq_query_0;
#[doc = "PLL_DIV_CLK_EN (rw) register accessor: SPLL DIV clock-gating configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`pll_div_clk_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pll_div_clk_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pll_div_clk_en`] module"]
pub type PLL_DIV_CLK_EN = crate::Reg<pll_div_clk_en::PLL_DIV_CLK_EN_SPEC>;
#[doc = "SPLL DIV clock-gating configuration register"]
pub mod pll_div_clk_en;
#[doc = "CTRL_CLK_OUT_EN (rw) register accessor: CLK_OUT_EN configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl_clk_out_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl_clk_out_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctrl_clk_out_en`] module"]
pub type CTRL_CLK_OUT_EN = crate::Reg<ctrl_clk_out_en::CTRL_CLK_OUT_EN_SPEC>;
#[doc = "CLK_OUT_EN configuration register"]
pub mod ctrl_clk_out_en;
#[doc = "CTRL_TICK_CONF (rw) register accessor: TICK configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl_tick_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl_tick_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctrl_tick_conf`] module"]
pub type CTRL_TICK_CONF = crate::Reg<ctrl_tick_conf::CTRL_TICK_CONF_SPEC>;
#[doc = "TICK configuration register"]
pub mod ctrl_tick_conf;
#[doc = "CTRL_32K_CONF (rw) register accessor: 32KHz clock configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl_32k_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl_32k_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctrl_32k_conf`] module"]
pub type CTRL_32K_CONF = crate::Reg<ctrl_32k_conf::CTRL_32K_CONF_SPEC>;
#[doc = "32KHz clock configuration register"]
pub mod ctrl_32k_conf;
#[doc = "SRAM_POWER_CONF (rw) register accessor: HP SRAM/ROM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sram_power_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sram_power_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sram_power_conf`] module"]
pub type SRAM_POWER_CONF = crate::Reg<sram_power_conf::SRAM_POWER_CONF_SPEC>;
#[doc = "HP SRAM/ROM configuration register"]
pub mod sram_power_conf;
#[doc = "RESET_EVENT_BYPASS (rw) register accessor: reset event bypass backdoor configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`reset_event_bypass::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`reset_event_bypass::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@reset_event_bypass`] module"]
pub type RESET_EVENT_BYPASS = crate::Reg<reset_event_bypass::RESET_EVENT_BYPASS_SPEC>;
#[doc = "reset event bypass backdoor configuration register"]
pub mod reset_event_bypass;
#[doc = "FPGA_DEBUG (rw) register accessor: fpga debug register\n\nYou can [`read`](crate::Reg::read) this register and get [`fpga_debug::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`fpga_debug::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fpga_debug`] module"]
pub type FPGA_DEBUG = crate::Reg<fpga_debug::FPGA_DEBUG_SPEC>;
#[doc = "fpga debug register"]
pub mod fpga_debug;
#[doc = "CLOCK_GATE (rw) register accessor: PCR clock gating configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`clock_gate::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clock_gate::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clock_gate`] module"]
pub type CLOCK_GATE = crate::Reg<clock_gate::CLOCK_GATE_SPEC>;
#[doc = "PCR clock gating configure register"]
pub mod clock_gate;
pub use crate::aes::{date, DATE};
