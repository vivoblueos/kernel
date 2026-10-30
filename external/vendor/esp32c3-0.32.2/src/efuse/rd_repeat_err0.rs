#[doc = "Register `RD_REPEAT_ERR0` reader"]
pub type R = crate::R<RD_REPEAT_ERR0_SPEC>;
#[doc = "Field `RD_DIS_ERR` reader - If any bit in RD_DIS is 1, then it indicates a programming error."]
pub type RD_DIS_ERR_R = crate::FieldReader;
#[doc = "Field `DIS_RTC_RAM_BOOT_ERR` reader - If DIS_RTC_RAM_BOOT is 1, then it indicates a programming error."]
pub type DIS_RTC_RAM_BOOT_ERR_R = crate::BitReader;
#[doc = "Field `DIS_ICACHE_ERR` reader - If DIS_ICACHE is 1, then it indicates a programming error."]
pub type DIS_ICACHE_ERR_R = crate::BitReader;
#[doc = "Field `DIS_USB_JTAG_ERR` reader - If DIS_USB_JTAG is 1, then it indicates a programming error."]
pub type DIS_USB_JTAG_ERR_R = crate::BitReader;
#[doc = "Field `DIS_DOWNLOAD_ICACHE_ERR` reader - If DIS_DOWNLOAD_ICACHE is 1, then it indicates a programming error."]
pub type DIS_DOWNLOAD_ICACHE_ERR_R = crate::BitReader;
#[doc = "Field `DIS_USB_DEVICE_ERR` reader - If DIS_USB_DEVICE is 1, then it indicates a programming error."]
pub type DIS_USB_DEVICE_ERR_R = crate::BitReader;
#[doc = "Field `DIS_FORCE_DOWNLOAD_ERR` reader - If DIS_FORCE_DOWNLOAD is 1, then it indicates a programming error."]
pub type DIS_FORCE_DOWNLOAD_ERR_R = crate::BitReader;
#[doc = "Field `RPT4_RESERVED6_ERR` reader - Reserved."]
pub type RPT4_RESERVED6_ERR_R = crate::BitReader;
#[doc = "Field `DIS_CAN_ERR` reader - If DIS_CAN is 1, then it indicates a programming error."]
pub type DIS_CAN_ERR_R = crate::BitReader;
#[doc = "Field `JTAG_SEL_ENABLE_ERR` reader - If JTAG_SEL_ENABLE is 1, then it indicates a programming error."]
pub type JTAG_SEL_ENABLE_ERR_R = crate::BitReader;
#[doc = "Field `SOFT_DIS_JTAG_ERR` reader - If SOFT_DIS_JTAG is 1, then it indicates a programming error."]
pub type SOFT_DIS_JTAG_ERR_R = crate::FieldReader;
#[doc = "Field `DIS_PAD_JTAG_ERR` reader - If DIS_PAD_JTAG is 1, then it indicates a programming error."]
pub type DIS_PAD_JTAG_ERR_R = crate::BitReader;
#[doc = "Field `DIS_DOWNLOAD_MANUAL_ENCRYPT_ERR` reader - If DIS_DOWNLOAD_MANUAL_ENCRYPT is 1, then it indicates a programming error."]
pub type DIS_DOWNLOAD_MANUAL_ENCRYPT_ERR_R = crate::BitReader;
#[doc = "Field `USB_DREFH_ERR` reader - If any bit in USB_DREFH is 1, then it indicates a programming error."]
pub type USB_DREFH_ERR_R = crate::FieldReader;
#[doc = "Field `USB_DREFL_ERR` reader - If any bit in USB_DREFL is 1, then it indicates a programming error."]
pub type USB_DREFL_ERR_R = crate::FieldReader;
#[doc = "Field `USB_EXCHG_PINS_ERR` reader - If USB_EXCHG_PINS is 1, then it indicates a programming error."]
pub type USB_EXCHG_PINS_ERR_R = crate::BitReader;
#[doc = "Field `VDD_SPI_AS_GPIO_ERR` reader - If VDD_SPI_AS_GPIO is 1, then it indicates a programming error."]
pub type VDD_SPI_AS_GPIO_ERR_R = crate::BitReader;
#[doc = "Field `BTLC_GPIO_ENABLE_ERR` reader - If any bit in BTLC_GPIO_ENABLE is 1, then it indicates a programming error."]
pub type BTLC_GPIO_ENABLE_ERR_R = crate::FieldReader;
#[doc = "Field `POWERGLITCH_EN_ERR` reader - If POWERGLITCH_EN is 1, then it indicates a programming error."]
pub type POWERGLITCH_EN_ERR_R = crate::BitReader;
#[doc = "Field `POWER_GLITCH_DSENSE_ERR` reader - If any bit in POWER_GLITCH_DSENSE is 1, then it indicates a programming error."]
pub type POWER_GLITCH_DSENSE_ERR_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:6 - If any bit in RD_DIS is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn rd_dis_err(&self) -> RD_DIS_ERR_R {
        RD_DIS_ERR_R::new((self.bits & 0x7f) as u8)
    }
    #[doc = "Bit 7 - If DIS_RTC_RAM_BOOT is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn dis_rtc_ram_boot_err(&self) -> DIS_RTC_RAM_BOOT_ERR_R {
        DIS_RTC_RAM_BOOT_ERR_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - If DIS_ICACHE is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn dis_icache_err(&self) -> DIS_ICACHE_ERR_R {
        DIS_ICACHE_ERR_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - If DIS_USB_JTAG is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn dis_usb_jtag_err(&self) -> DIS_USB_JTAG_ERR_R {
        DIS_USB_JTAG_ERR_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - If DIS_DOWNLOAD_ICACHE is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn dis_download_icache_err(&self) -> DIS_DOWNLOAD_ICACHE_ERR_R {
        DIS_DOWNLOAD_ICACHE_ERR_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - If DIS_USB_DEVICE is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn dis_usb_device_err(&self) -> DIS_USB_DEVICE_ERR_R {
        DIS_USB_DEVICE_ERR_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - If DIS_FORCE_DOWNLOAD is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn dis_force_download_err(&self) -> DIS_FORCE_DOWNLOAD_ERR_R {
        DIS_FORCE_DOWNLOAD_ERR_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Reserved."]
    #[inline(always)]
    pub fn rpt4_reserved6_err(&self) -> RPT4_RESERVED6_ERR_R {
        RPT4_RESERVED6_ERR_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - If DIS_CAN is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn dis_can_err(&self) -> DIS_CAN_ERR_R {
        DIS_CAN_ERR_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - If JTAG_SEL_ENABLE is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn jtag_sel_enable_err(&self) -> JTAG_SEL_ENABLE_ERR_R {
        JTAG_SEL_ENABLE_ERR_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 16:18 - If SOFT_DIS_JTAG is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn soft_dis_jtag_err(&self) -> SOFT_DIS_JTAG_ERR_R {
        SOFT_DIS_JTAG_ERR_R::new(((self.bits >> 16) & 7) as u8)
    }
    #[doc = "Bit 19 - If DIS_PAD_JTAG is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn dis_pad_jtag_err(&self) -> DIS_PAD_JTAG_ERR_R {
        DIS_PAD_JTAG_ERR_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - If DIS_DOWNLOAD_MANUAL_ENCRYPT is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn dis_download_manual_encrypt_err(&self) -> DIS_DOWNLOAD_MANUAL_ENCRYPT_ERR_R {
        DIS_DOWNLOAD_MANUAL_ENCRYPT_ERR_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bits 21:22 - If any bit in USB_DREFH is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn usb_drefh_err(&self) -> USB_DREFH_ERR_R {
        USB_DREFH_ERR_R::new(((self.bits >> 21) & 3) as u8)
    }
    #[doc = "Bits 23:24 - If any bit in USB_DREFL is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn usb_drefl_err(&self) -> USB_DREFL_ERR_R {
        USB_DREFL_ERR_R::new(((self.bits >> 23) & 3) as u8)
    }
    #[doc = "Bit 25 - If USB_EXCHG_PINS is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn usb_exchg_pins_err(&self) -> USB_EXCHG_PINS_ERR_R {
        USB_EXCHG_PINS_ERR_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - If VDD_SPI_AS_GPIO is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn vdd_spi_as_gpio_err(&self) -> VDD_SPI_AS_GPIO_ERR_R {
        VDD_SPI_AS_GPIO_ERR_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bits 27:28 - If any bit in BTLC_GPIO_ENABLE is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn btlc_gpio_enable_err(&self) -> BTLC_GPIO_ENABLE_ERR_R {
        BTLC_GPIO_ENABLE_ERR_R::new(((self.bits >> 27) & 3) as u8)
    }
    #[doc = "Bit 29 - If POWERGLITCH_EN is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn powerglitch_en_err(&self) -> POWERGLITCH_EN_ERR_R {
        POWERGLITCH_EN_ERR_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bits 30:31 - If any bit in POWER_GLITCH_DSENSE is 1, then it indicates a programming error."]
    #[inline(always)]
    pub fn power_glitch_dsense_err(&self) -> POWER_GLITCH_DSENSE_ERR_R {
        POWER_GLITCH_DSENSE_ERR_R::new(((self.bits >> 30) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_REPEAT_ERR0")
            .field("rd_dis_err", &self.rd_dis_err())
            .field("dis_rtc_ram_boot_err", &self.dis_rtc_ram_boot_err())
            .field("dis_icache_err", &self.dis_icache_err())
            .field("dis_usb_jtag_err", &self.dis_usb_jtag_err())
            .field("dis_download_icache_err", &self.dis_download_icache_err())
            .field("dis_usb_device_err", &self.dis_usb_device_err())
            .field("dis_force_download_err", &self.dis_force_download_err())
            .field("rpt4_reserved6_err", &self.rpt4_reserved6_err())
            .field("dis_can_err", &self.dis_can_err())
            .field("jtag_sel_enable_err", &self.jtag_sel_enable_err())
            .field("soft_dis_jtag_err", &self.soft_dis_jtag_err())
            .field("dis_pad_jtag_err", &self.dis_pad_jtag_err())
            .field(
                "dis_download_manual_encrypt_err",
                &self.dis_download_manual_encrypt_err(),
            )
            .field("usb_drefh_err", &self.usb_drefh_err())
            .field("usb_drefl_err", &self.usb_drefl_err())
            .field("usb_exchg_pins_err", &self.usb_exchg_pins_err())
            .field("vdd_spi_as_gpio_err", &self.vdd_spi_as_gpio_err())
            .field("btlc_gpio_enable_err", &self.btlc_gpio_enable_err())
            .field("powerglitch_en_err", &self.powerglitch_en_err())
            .field("power_glitch_dsense_err", &self.power_glitch_dsense_err())
            .finish()
    }
}
#[doc = "Programming error record register 0 of BLOCK0.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_err0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_REPEAT_ERR0_SPEC;
impl crate::RegisterSpec for RD_REPEAT_ERR0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_repeat_err0::R`](R) reader structure"]
impl crate::Readable for RD_REPEAT_ERR0_SPEC {}
#[doc = "`reset()` method sets RD_REPEAT_ERR0 to value 0"]
impl crate::Resettable for RD_REPEAT_ERR0_SPEC {}
