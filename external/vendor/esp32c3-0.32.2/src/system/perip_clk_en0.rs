#[doc = "Register `PERIP_CLK_EN0` reader"]
pub type R = crate::R<PERIP_CLK_EN0_SPEC>;
#[doc = "Register `PERIP_CLK_EN0` writer"]
pub type W = crate::W<PERIP_CLK_EN0_SPEC>;
#[doc = "Field `TIMERS_CLK_EN` reader - reg_timers_clk_en"]
pub type TIMERS_CLK_EN_R = crate::BitReader;
#[doc = "Field `TIMERS_CLK_EN` writer - reg_timers_clk_en"]
pub type TIMERS_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI01_CLK_EN` reader - reg_spi01_clk_en"]
pub type SPI01_CLK_EN_R = crate::BitReader;
#[doc = "Field `SPI01_CLK_EN` writer - reg_spi01_clk_en"]
pub type SPI01_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UART_CLK_EN` reader - reg_uart_clk_en"]
pub type UART_CLK_EN_R = crate::BitReader;
#[doc = "Field `UART_CLK_EN` writer - reg_uart_clk_en"]
pub type UART_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WDG_CLK_EN` reader - reg_wdg_clk_en"]
pub type WDG_CLK_EN_R = crate::BitReader;
#[doc = "Field `WDG_CLK_EN` writer - reg_wdg_clk_en"]
pub type WDG_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UART1_CLK_EN` reader - reg_uart1_clk_en"]
pub type UART1_CLK_EN_R = crate::BitReader;
#[doc = "Field `UART1_CLK_EN` writer - reg_uart1_clk_en"]
pub type UART1_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI2_CLK_EN` reader - reg_spi2_clk_en"]
pub type SPI2_CLK_EN_R = crate::BitReader;
#[doc = "Field `SPI2_CLK_EN` writer - reg_spi2_clk_en"]
pub type SPI2_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2C_EXT0_CLK_EN` reader - reg_ext0_clk_en"]
pub type I2C_EXT0_CLK_EN_R = crate::BitReader;
#[doc = "Field `I2C_EXT0_CLK_EN` writer - reg_ext0_clk_en"]
pub type I2C_EXT0_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UHCI0_CLK_EN` reader - reg_uhci0_clk_en"]
pub type UHCI0_CLK_EN_R = crate::BitReader;
#[doc = "Field `UHCI0_CLK_EN` writer - reg_uhci0_clk_en"]
pub type UHCI0_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RMT_CLK_EN` reader - reg_rmt_clk_en"]
pub type RMT_CLK_EN_R = crate::BitReader;
#[doc = "Field `RMT_CLK_EN` writer - reg_rmt_clk_en"]
pub type RMT_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PCNT_CLK_EN` reader - reg_pcnt_clk_en"]
pub type PCNT_CLK_EN_R = crate::BitReader;
#[doc = "Field `PCNT_CLK_EN` writer - reg_pcnt_clk_en"]
pub type PCNT_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LEDC_CLK_EN` reader - reg_ledc_clk_en"]
pub type LEDC_CLK_EN_R = crate::BitReader;
#[doc = "Field `LEDC_CLK_EN` writer - reg_ledc_clk_en"]
pub type LEDC_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UHCI1_CLK_EN` reader - reg_uhci1_clk_en"]
pub type UHCI1_CLK_EN_R = crate::BitReader;
#[doc = "Field `UHCI1_CLK_EN` writer - reg_uhci1_clk_en"]
pub type UHCI1_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMERGROUP_CLK_EN` reader - reg_timergroup_clk_en"]
pub type TIMERGROUP_CLK_EN_R = crate::BitReader;
#[doc = "Field `TIMERGROUP_CLK_EN` writer - reg_timergroup_clk_en"]
pub type TIMERGROUP_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EFUSE_CLK_EN` reader - reg_efuse_clk_en"]
pub type EFUSE_CLK_EN_R = crate::BitReader;
#[doc = "Field `EFUSE_CLK_EN` writer - reg_efuse_clk_en"]
pub type EFUSE_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMERGROUP1_CLK_EN` reader - reg_timergroup1_clk_en"]
pub type TIMERGROUP1_CLK_EN_R = crate::BitReader;
#[doc = "Field `TIMERGROUP1_CLK_EN` writer - reg_timergroup1_clk_en"]
pub type TIMERGROUP1_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI3_CLK_EN` reader - reg_spi3_clk_en"]
pub type SPI3_CLK_EN_R = crate::BitReader;
#[doc = "Field `SPI3_CLK_EN` writer - reg_spi3_clk_en"]
pub type SPI3_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PWM0_CLK_EN` reader - reg_pwm0_clk_en"]
pub type PWM0_CLK_EN_R = crate::BitReader;
#[doc = "Field `PWM0_CLK_EN` writer - reg_pwm0_clk_en"]
pub type PWM0_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXT1_CLK_EN` reader - reg_ext1_clk_en"]
pub type EXT1_CLK_EN_R = crate::BitReader;
#[doc = "Field `EXT1_CLK_EN` writer - reg_ext1_clk_en"]
pub type EXT1_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TWAI_CLK_EN` reader - reg_can_clk_en"]
pub type TWAI_CLK_EN_R = crate::BitReader;
#[doc = "Field `TWAI_CLK_EN` writer - reg_can_clk_en"]
pub type TWAI_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PWM1_CLK_EN` reader - reg_pwm1_clk_en"]
pub type PWM1_CLK_EN_R = crate::BitReader;
#[doc = "Field `PWM1_CLK_EN` writer - reg_pwm1_clk_en"]
pub type PWM1_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2S0_CLK_EN` reader - reg_i2s1_clk_en"]
pub type I2S0_CLK_EN_R = crate::BitReader;
#[doc = "Field `I2S0_CLK_EN` writer - reg_i2s1_clk_en"]
pub type I2S0_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI2_DMA_CLK_EN` reader - reg_spi2_dma_clk_en"]
pub type SPI2_DMA_CLK_EN_R = crate::BitReader;
#[doc = "Field `SPI2_DMA_CLK_EN` writer - reg_spi2_dma_clk_en"]
pub type SPI2_DMA_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USB_DEVICE_CLK_EN` reader - reg_usb_device_clk_en"]
pub type USB_DEVICE_CLK_EN_R = crate::BitReader;
#[doc = "Field `USB_DEVICE_CLK_EN` writer - reg_usb_device_clk_en"]
pub type USB_DEVICE_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UART_MEM_CLK_EN` reader - reg_uart_mem_clk_en"]
pub type UART_MEM_CLK_EN_R = crate::BitReader;
#[doc = "Field `UART_MEM_CLK_EN` writer - reg_uart_mem_clk_en"]
pub type UART_MEM_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PWM2_CLK_EN` reader - reg_pwm2_clk_en"]
pub type PWM2_CLK_EN_R = crate::BitReader;
#[doc = "Field `PWM2_CLK_EN` writer - reg_pwm2_clk_en"]
pub type PWM2_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PWM3_CLK_EN` reader - reg_pwm3_clk_en"]
pub type PWM3_CLK_EN_R = crate::BitReader;
#[doc = "Field `PWM3_CLK_EN` writer - reg_pwm3_clk_en"]
pub type PWM3_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI3_DMA_CLK_EN` reader - reg_spi3_dma_clk_en"]
pub type SPI3_DMA_CLK_EN_R = crate::BitReader;
#[doc = "Field `SPI3_DMA_CLK_EN` writer - reg_spi3_dma_clk_en"]
pub type SPI3_DMA_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `APB_SARADC_CLK_EN` reader - reg_apb_saradc_clk_en"]
pub type APB_SARADC_CLK_EN_R = crate::BitReader;
#[doc = "Field `APB_SARADC_CLK_EN` writer - reg_apb_saradc_clk_en"]
pub type APB_SARADC_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SYSTIMER_CLK_EN` reader - reg_systimer_clk_en"]
pub type SYSTIMER_CLK_EN_R = crate::BitReader;
#[doc = "Field `SYSTIMER_CLK_EN` writer - reg_systimer_clk_en"]
pub type SYSTIMER_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADC2_ARB_CLK_EN` reader - reg_adc2_arb_clk_en"]
pub type ADC2_ARB_CLK_EN_R = crate::BitReader;
#[doc = "Field `ADC2_ARB_CLK_EN` writer - reg_adc2_arb_clk_en"]
pub type ADC2_ARB_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPI4_CLK_EN` reader - reg_spi4_clk_en"]
pub type SPI4_CLK_EN_R = crate::BitReader;
#[doc = "Field `SPI4_CLK_EN` writer - reg_spi4_clk_en"]
pub type SPI4_CLK_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - reg_timers_clk_en"]
    #[inline(always)]
    pub fn timers_clk_en(&self) -> TIMERS_CLK_EN_R {
        TIMERS_CLK_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - reg_spi01_clk_en"]
    #[inline(always)]
    pub fn spi01_clk_en(&self) -> SPI01_CLK_EN_R {
        SPI01_CLK_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - reg_uart_clk_en"]
    #[inline(always)]
    pub fn uart_clk_en(&self) -> UART_CLK_EN_R {
        UART_CLK_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - reg_wdg_clk_en"]
    #[inline(always)]
    pub fn wdg_clk_en(&self) -> WDG_CLK_EN_R {
        WDG_CLK_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 5 - reg_uart1_clk_en"]
    #[inline(always)]
    pub fn uart1_clk_en(&self) -> UART1_CLK_EN_R {
        UART1_CLK_EN_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - reg_spi2_clk_en"]
    #[inline(always)]
    pub fn spi2_clk_en(&self) -> SPI2_CLK_EN_R {
        SPI2_CLK_EN_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - reg_ext0_clk_en"]
    #[inline(always)]
    pub fn i2c_ext0_clk_en(&self) -> I2C_EXT0_CLK_EN_R {
        I2C_EXT0_CLK_EN_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - reg_uhci0_clk_en"]
    #[inline(always)]
    pub fn uhci0_clk_en(&self) -> UHCI0_CLK_EN_R {
        UHCI0_CLK_EN_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - reg_rmt_clk_en"]
    #[inline(always)]
    pub fn rmt_clk_en(&self) -> RMT_CLK_EN_R {
        RMT_CLK_EN_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - reg_pcnt_clk_en"]
    #[inline(always)]
    pub fn pcnt_clk_en(&self) -> PCNT_CLK_EN_R {
        PCNT_CLK_EN_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - reg_ledc_clk_en"]
    #[inline(always)]
    pub fn ledc_clk_en(&self) -> LEDC_CLK_EN_R {
        LEDC_CLK_EN_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - reg_uhci1_clk_en"]
    #[inline(always)]
    pub fn uhci1_clk_en(&self) -> UHCI1_CLK_EN_R {
        UHCI1_CLK_EN_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - reg_timergroup_clk_en"]
    #[inline(always)]
    pub fn timergroup_clk_en(&self) -> TIMERGROUP_CLK_EN_R {
        TIMERGROUP_CLK_EN_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - reg_efuse_clk_en"]
    #[inline(always)]
    pub fn efuse_clk_en(&self) -> EFUSE_CLK_EN_R {
        EFUSE_CLK_EN_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - reg_timergroup1_clk_en"]
    #[inline(always)]
    pub fn timergroup1_clk_en(&self) -> TIMERGROUP1_CLK_EN_R {
        TIMERGROUP1_CLK_EN_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - reg_spi3_clk_en"]
    #[inline(always)]
    pub fn spi3_clk_en(&self) -> SPI3_CLK_EN_R {
        SPI3_CLK_EN_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - reg_pwm0_clk_en"]
    #[inline(always)]
    pub fn pwm0_clk_en(&self) -> PWM0_CLK_EN_R {
        PWM0_CLK_EN_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - reg_ext1_clk_en"]
    #[inline(always)]
    pub fn ext1_clk_en(&self) -> EXT1_CLK_EN_R {
        EXT1_CLK_EN_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - reg_can_clk_en"]
    #[inline(always)]
    pub fn twai_clk_en(&self) -> TWAI_CLK_EN_R {
        TWAI_CLK_EN_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - reg_pwm1_clk_en"]
    #[inline(always)]
    pub fn pwm1_clk_en(&self) -> PWM1_CLK_EN_R {
        PWM1_CLK_EN_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - reg_i2s1_clk_en"]
    #[inline(always)]
    pub fn i2s0_clk_en(&self) -> I2S0_CLK_EN_R {
        I2S0_CLK_EN_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - reg_spi2_dma_clk_en"]
    #[inline(always)]
    pub fn spi2_dma_clk_en(&self) -> SPI2_DMA_CLK_EN_R {
        SPI2_DMA_CLK_EN_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - reg_usb_device_clk_en"]
    #[inline(always)]
    pub fn usb_device_clk_en(&self) -> USB_DEVICE_CLK_EN_R {
        USB_DEVICE_CLK_EN_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - reg_uart_mem_clk_en"]
    #[inline(always)]
    pub fn uart_mem_clk_en(&self) -> UART_MEM_CLK_EN_R {
        UART_MEM_CLK_EN_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - reg_pwm2_clk_en"]
    #[inline(always)]
    pub fn pwm2_clk_en(&self) -> PWM2_CLK_EN_R {
        PWM2_CLK_EN_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - reg_pwm3_clk_en"]
    #[inline(always)]
    pub fn pwm3_clk_en(&self) -> PWM3_CLK_EN_R {
        PWM3_CLK_EN_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - reg_spi3_dma_clk_en"]
    #[inline(always)]
    pub fn spi3_dma_clk_en(&self) -> SPI3_DMA_CLK_EN_R {
        SPI3_DMA_CLK_EN_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - reg_apb_saradc_clk_en"]
    #[inline(always)]
    pub fn apb_saradc_clk_en(&self) -> APB_SARADC_CLK_EN_R {
        APB_SARADC_CLK_EN_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - reg_systimer_clk_en"]
    #[inline(always)]
    pub fn systimer_clk_en(&self) -> SYSTIMER_CLK_EN_R {
        SYSTIMER_CLK_EN_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - reg_adc2_arb_clk_en"]
    #[inline(always)]
    pub fn adc2_arb_clk_en(&self) -> ADC2_ARB_CLK_EN_R {
        ADC2_ARB_CLK_EN_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - reg_spi4_clk_en"]
    #[inline(always)]
    pub fn spi4_clk_en(&self) -> SPI4_CLK_EN_R {
        SPI4_CLK_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PERIP_CLK_EN0")
            .field("timers_clk_en", &self.timers_clk_en())
            .field("spi01_clk_en", &self.spi01_clk_en())
            .field("uart_clk_en", &self.uart_clk_en())
            .field("wdg_clk_en", &self.wdg_clk_en())
            .field("uart1_clk_en", &self.uart1_clk_en())
            .field("spi2_clk_en", &self.spi2_clk_en())
            .field("i2c_ext0_clk_en", &self.i2c_ext0_clk_en())
            .field("uhci0_clk_en", &self.uhci0_clk_en())
            .field("rmt_clk_en", &self.rmt_clk_en())
            .field("pcnt_clk_en", &self.pcnt_clk_en())
            .field("ledc_clk_en", &self.ledc_clk_en())
            .field("uhci1_clk_en", &self.uhci1_clk_en())
            .field("timergroup_clk_en", &self.timergroup_clk_en())
            .field("efuse_clk_en", &self.efuse_clk_en())
            .field("timergroup1_clk_en", &self.timergroup1_clk_en())
            .field("spi3_clk_en", &self.spi3_clk_en())
            .field("pwm0_clk_en", &self.pwm0_clk_en())
            .field("ext1_clk_en", &self.ext1_clk_en())
            .field("twai_clk_en", &self.twai_clk_en())
            .field("pwm1_clk_en", &self.pwm1_clk_en())
            .field("i2s0_clk_en", &self.i2s0_clk_en())
            .field("spi2_dma_clk_en", &self.spi2_dma_clk_en())
            .field("usb_device_clk_en", &self.usb_device_clk_en())
            .field("uart_mem_clk_en", &self.uart_mem_clk_en())
            .field("pwm2_clk_en", &self.pwm2_clk_en())
            .field("pwm3_clk_en", &self.pwm3_clk_en())
            .field("spi3_dma_clk_en", &self.spi3_dma_clk_en())
            .field("apb_saradc_clk_en", &self.apb_saradc_clk_en())
            .field("systimer_clk_en", &self.systimer_clk_en())
            .field("adc2_arb_clk_en", &self.adc2_arb_clk_en())
            .field("spi4_clk_en", &self.spi4_clk_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - reg_timers_clk_en"]
    #[inline(always)]
    pub fn timers_clk_en(&mut self) -> TIMERS_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        TIMERS_CLK_EN_W::new(self, 0)
    }
    #[doc = "Bit 1 - reg_spi01_clk_en"]
    #[inline(always)]
    pub fn spi01_clk_en(&mut self) -> SPI01_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        SPI01_CLK_EN_W::new(self, 1)
    }
    #[doc = "Bit 2 - reg_uart_clk_en"]
    #[inline(always)]
    pub fn uart_clk_en(&mut self) -> UART_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        UART_CLK_EN_W::new(self, 2)
    }
    #[doc = "Bit 3 - reg_wdg_clk_en"]
    #[inline(always)]
    pub fn wdg_clk_en(&mut self) -> WDG_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        WDG_CLK_EN_W::new(self, 3)
    }
    #[doc = "Bit 5 - reg_uart1_clk_en"]
    #[inline(always)]
    pub fn uart1_clk_en(&mut self) -> UART1_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        UART1_CLK_EN_W::new(self, 5)
    }
    #[doc = "Bit 6 - reg_spi2_clk_en"]
    #[inline(always)]
    pub fn spi2_clk_en(&mut self) -> SPI2_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        SPI2_CLK_EN_W::new(self, 6)
    }
    #[doc = "Bit 7 - reg_ext0_clk_en"]
    #[inline(always)]
    pub fn i2c_ext0_clk_en(&mut self) -> I2C_EXT0_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        I2C_EXT0_CLK_EN_W::new(self, 7)
    }
    #[doc = "Bit 8 - reg_uhci0_clk_en"]
    #[inline(always)]
    pub fn uhci0_clk_en(&mut self) -> UHCI0_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        UHCI0_CLK_EN_W::new(self, 8)
    }
    #[doc = "Bit 9 - reg_rmt_clk_en"]
    #[inline(always)]
    pub fn rmt_clk_en(&mut self) -> RMT_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        RMT_CLK_EN_W::new(self, 9)
    }
    #[doc = "Bit 10 - reg_pcnt_clk_en"]
    #[inline(always)]
    pub fn pcnt_clk_en(&mut self) -> PCNT_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        PCNT_CLK_EN_W::new(self, 10)
    }
    #[doc = "Bit 11 - reg_ledc_clk_en"]
    #[inline(always)]
    pub fn ledc_clk_en(&mut self) -> LEDC_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        LEDC_CLK_EN_W::new(self, 11)
    }
    #[doc = "Bit 12 - reg_uhci1_clk_en"]
    #[inline(always)]
    pub fn uhci1_clk_en(&mut self) -> UHCI1_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        UHCI1_CLK_EN_W::new(self, 12)
    }
    #[doc = "Bit 13 - reg_timergroup_clk_en"]
    #[inline(always)]
    pub fn timergroup_clk_en(&mut self) -> TIMERGROUP_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        TIMERGROUP_CLK_EN_W::new(self, 13)
    }
    #[doc = "Bit 14 - reg_efuse_clk_en"]
    #[inline(always)]
    pub fn efuse_clk_en(&mut self) -> EFUSE_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        EFUSE_CLK_EN_W::new(self, 14)
    }
    #[doc = "Bit 15 - reg_timergroup1_clk_en"]
    #[inline(always)]
    pub fn timergroup1_clk_en(&mut self) -> TIMERGROUP1_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        TIMERGROUP1_CLK_EN_W::new(self, 15)
    }
    #[doc = "Bit 16 - reg_spi3_clk_en"]
    #[inline(always)]
    pub fn spi3_clk_en(&mut self) -> SPI3_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        SPI3_CLK_EN_W::new(self, 16)
    }
    #[doc = "Bit 17 - reg_pwm0_clk_en"]
    #[inline(always)]
    pub fn pwm0_clk_en(&mut self) -> PWM0_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        PWM0_CLK_EN_W::new(self, 17)
    }
    #[doc = "Bit 18 - reg_ext1_clk_en"]
    #[inline(always)]
    pub fn ext1_clk_en(&mut self) -> EXT1_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        EXT1_CLK_EN_W::new(self, 18)
    }
    #[doc = "Bit 19 - reg_can_clk_en"]
    #[inline(always)]
    pub fn twai_clk_en(&mut self) -> TWAI_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        TWAI_CLK_EN_W::new(self, 19)
    }
    #[doc = "Bit 20 - reg_pwm1_clk_en"]
    #[inline(always)]
    pub fn pwm1_clk_en(&mut self) -> PWM1_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        PWM1_CLK_EN_W::new(self, 20)
    }
    #[doc = "Bit 21 - reg_i2s1_clk_en"]
    #[inline(always)]
    pub fn i2s0_clk_en(&mut self) -> I2S0_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        I2S0_CLK_EN_W::new(self, 21)
    }
    #[doc = "Bit 22 - reg_spi2_dma_clk_en"]
    #[inline(always)]
    pub fn spi2_dma_clk_en(&mut self) -> SPI2_DMA_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        SPI2_DMA_CLK_EN_W::new(self, 22)
    }
    #[doc = "Bit 23 - reg_usb_device_clk_en"]
    #[inline(always)]
    pub fn usb_device_clk_en(&mut self) -> USB_DEVICE_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        USB_DEVICE_CLK_EN_W::new(self, 23)
    }
    #[doc = "Bit 24 - reg_uart_mem_clk_en"]
    #[inline(always)]
    pub fn uart_mem_clk_en(&mut self) -> UART_MEM_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        UART_MEM_CLK_EN_W::new(self, 24)
    }
    #[doc = "Bit 25 - reg_pwm2_clk_en"]
    #[inline(always)]
    pub fn pwm2_clk_en(&mut self) -> PWM2_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        PWM2_CLK_EN_W::new(self, 25)
    }
    #[doc = "Bit 26 - reg_pwm3_clk_en"]
    #[inline(always)]
    pub fn pwm3_clk_en(&mut self) -> PWM3_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        PWM3_CLK_EN_W::new(self, 26)
    }
    #[doc = "Bit 27 - reg_spi3_dma_clk_en"]
    #[inline(always)]
    pub fn spi3_dma_clk_en(&mut self) -> SPI3_DMA_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        SPI3_DMA_CLK_EN_W::new(self, 27)
    }
    #[doc = "Bit 28 - reg_apb_saradc_clk_en"]
    #[inline(always)]
    pub fn apb_saradc_clk_en(&mut self) -> APB_SARADC_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        APB_SARADC_CLK_EN_W::new(self, 28)
    }
    #[doc = "Bit 29 - reg_systimer_clk_en"]
    #[inline(always)]
    pub fn systimer_clk_en(&mut self) -> SYSTIMER_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        SYSTIMER_CLK_EN_W::new(self, 29)
    }
    #[doc = "Bit 30 - reg_adc2_arb_clk_en"]
    #[inline(always)]
    pub fn adc2_arb_clk_en(&mut self) -> ADC2_ARB_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        ADC2_ARB_CLK_EN_W::new(self, 30)
    }
    #[doc = "Bit 31 - reg_spi4_clk_en"]
    #[inline(always)]
    pub fn spi4_clk_en(&mut self) -> SPI4_CLK_EN_W<'_, PERIP_CLK_EN0_SPEC> {
        SPI4_CLK_EN_W::new(self, 31)
    }
}
#[doc = "peripheral clock gating register\n\nYou can [`read`](crate::Reg::read) this register and get [`perip_clk_en0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`perip_clk_en0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PERIP_CLK_EN0_SPEC;
impl crate::RegisterSpec for PERIP_CLK_EN0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`perip_clk_en0::R`](R) reader structure"]
impl crate::Readable for PERIP_CLK_EN0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`perip_clk_en0::W`](W) writer structure"]
impl crate::Writable for PERIP_CLK_EN0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PERIP_CLK_EN0 to value 0xf9c1_e06f"]
impl crate::Resettable for PERIP_CLK_EN0_SPEC {
    const RESET_VALUE: u32 = 0xf9c1_e06f;
}
