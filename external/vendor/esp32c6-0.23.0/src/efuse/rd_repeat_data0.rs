#[doc = "Register `RD_REPEAT_DATA0` reader"]
pub type R = crate::R<RD_REPEAT_DATA0_SPEC>;
#[doc = "Field `RD_DIS` reader - Represents whether reading of individual eFuse block(block4~block10) is disabled or enabled. 1: disabled. 0: enabled."]
pub type RD_DIS_R = crate::FieldReader;
#[doc = "Field `SWAP_UART_SDIO_EN` reader - Represents whether pad of uart and sdio is swapped or not. 1: swapped. 0: not swapped."]
pub type SWAP_UART_SDIO_EN_R = crate::BitReader;
#[doc = "Field `DIS_ICACHE` reader - Represents whether icache is disabled or enabled. 1: disabled. 0: enabled."]
pub type DIS_ICACHE_R = crate::BitReader;
#[doc = "Field `DIS_USB_JTAG` reader - Represents whether the function of usb switch to jtag is disabled or enabled. 1: disabled. 0: enabled."]
pub type DIS_USB_JTAG_R = crate::BitReader;
#[doc = "Field `DIS_DOWNLOAD_ICACHE` reader - Represents whether icache is disabled or enabled in Download mode. 1: disabled. 0: enabled."]
pub type DIS_DOWNLOAD_ICACHE_R = crate::BitReader;
#[doc = "Field `DIS_USB_SERIAL_JTAG` reader - Represents whether USB-Serial-JTAG is disabled or enabled. 1: disabled. 0: enabled."]
pub type DIS_USB_SERIAL_JTAG_R = crate::BitReader;
#[doc = "Field `DIS_FORCE_DOWNLOAD` reader - Represents whether the function that forces chip into download mode is disabled or enabled. 1: disabled. 0: enabled."]
pub type DIS_FORCE_DOWNLOAD_R = crate::BitReader;
#[doc = "Field `SPI_DOWNLOAD_MSPI_DIS` reader - Represents whether SPI0 controller during boot_mode_download is disabled or enabled. 1: disabled. 0: enabled."]
pub type SPI_DOWNLOAD_MSPI_DIS_R = crate::BitReader;
#[doc = "Field `DIS_CAN` reader - Represents whether TWAI function is disabled or enabled. 1: disabled. 0: enabled."]
pub type DIS_CAN_R = crate::BitReader;
#[doc = "Field `JTAG_SEL_ENABLE` reader - Represents whether the selection between usb_to_jtag and pad_to_jtag through strapping gpio15 when both EFUSE_DIS_PAD_JTAG and EFUSE_DIS_USB_JTAG are equal to 0 is enabled or disabled. 1: enabled. 0: disabled."]
pub type JTAG_SEL_ENABLE_R = crate::BitReader;
#[doc = "Field `SOFT_DIS_JTAG` reader - Represents whether JTAG is disabled in soft way. Odd number: disabled. Even number: enabled."]
pub type SOFT_DIS_JTAG_R = crate::FieldReader;
#[doc = "Field `DIS_PAD_JTAG` reader - Represents whether JTAG is disabled in the hard way(permanently). 1: disabled. 0: enabled."]
pub type DIS_PAD_JTAG_R = crate::BitReader;
#[doc = "Field `DIS_DOWNLOAD_MANUAL_ENCRYPT` reader - Represents whether flash encrypt function is disabled or enabled(except in SPI boot mode). 1: disabled. 0: enabled."]
pub type DIS_DOWNLOAD_MANUAL_ENCRYPT_R = crate::BitReader;
#[doc = "Field `USB_DREFH` reader - Represents the single-end input threhold vrefh, 1.76 V to 2 V with step of 80 mV."]
pub type USB_DREFH_R = crate::FieldReader;
#[doc = "Field `USB_DREFL` reader - Represents the single-end input threhold vrefl, 1.76 V to 2 V with step of 80 mV."]
pub type USB_DREFL_R = crate::FieldReader;
#[doc = "Field `USB_EXCHG_PINS` reader - Represents whether the D+ and D- pins is exchanged. 1: exchanged. 0: not exchanged."]
pub type USB_EXCHG_PINS_R = crate::BitReader;
#[doc = "Field `VDD_SPI_AS_GPIO` reader - Represents whether vdd spi pin is functioned as gpio. 1: functioned. 0: not functioned."]
pub type VDD_SPI_AS_GPIO_R = crate::BitReader;
#[doc = "Field `RPT4_RESERVED0_2` reader - Reserved."]
pub type RPT4_RESERVED0_2_R = crate::FieldReader;
#[doc = "Field `RPT4_RESERVED0_1` reader - Reserved."]
pub type RPT4_RESERVED0_1_R = crate::BitReader;
#[doc = "Field `RPT4_RESERVED0_0` reader - Reserved."]
pub type RPT4_RESERVED0_0_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:6 - Represents whether reading of individual eFuse block(block4~block10) is disabled or enabled. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn rd_dis(&self) -> RD_DIS_R {
        RD_DIS_R::new((self.bits & 0x7f) as u8)
    }
    #[doc = "Bit 7 - Represents whether pad of uart and sdio is swapped or not. 1: swapped. 0: not swapped."]
    #[inline(always)]
    pub fn swap_uart_sdio_en(&self) -> SWAP_UART_SDIO_EN_R {
        SWAP_UART_SDIO_EN_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Represents whether icache is disabled or enabled. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn dis_icache(&self) -> DIS_ICACHE_R {
        DIS_ICACHE_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Represents whether the function of usb switch to jtag is disabled or enabled. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn dis_usb_jtag(&self) -> DIS_USB_JTAG_R {
        DIS_USB_JTAG_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Represents whether icache is disabled or enabled in Download mode. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn dis_download_icache(&self) -> DIS_DOWNLOAD_ICACHE_R {
        DIS_DOWNLOAD_ICACHE_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Represents whether USB-Serial-JTAG is disabled or enabled. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn dis_usb_serial_jtag(&self) -> DIS_USB_SERIAL_JTAG_R {
        DIS_USB_SERIAL_JTAG_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Represents whether the function that forces chip into download mode is disabled or enabled. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn dis_force_download(&self) -> DIS_FORCE_DOWNLOAD_R {
        DIS_FORCE_DOWNLOAD_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Represents whether SPI0 controller during boot_mode_download is disabled or enabled. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn spi_download_mspi_dis(&self) -> SPI_DOWNLOAD_MSPI_DIS_R {
        SPI_DOWNLOAD_MSPI_DIS_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Represents whether TWAI function is disabled or enabled. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn dis_can(&self) -> DIS_CAN_R {
        DIS_CAN_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Represents whether the selection between usb_to_jtag and pad_to_jtag through strapping gpio15 when both EFUSE_DIS_PAD_JTAG and EFUSE_DIS_USB_JTAG are equal to 0 is enabled or disabled. 1: enabled. 0: disabled."]
    #[inline(always)]
    pub fn jtag_sel_enable(&self) -> JTAG_SEL_ENABLE_R {
        JTAG_SEL_ENABLE_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 16:18 - Represents whether JTAG is disabled in soft way. Odd number: disabled. Even number: enabled."]
    #[inline(always)]
    pub fn soft_dis_jtag(&self) -> SOFT_DIS_JTAG_R {
        SOFT_DIS_JTAG_R::new(((self.bits >> 16) & 7) as u8)
    }
    #[doc = "Bit 19 - Represents whether JTAG is disabled in the hard way(permanently). 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn dis_pad_jtag(&self) -> DIS_PAD_JTAG_R {
        DIS_PAD_JTAG_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Represents whether flash encrypt function is disabled or enabled(except in SPI boot mode). 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn dis_download_manual_encrypt(&self) -> DIS_DOWNLOAD_MANUAL_ENCRYPT_R {
        DIS_DOWNLOAD_MANUAL_ENCRYPT_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bits 21:22 - Represents the single-end input threhold vrefh, 1.76 V to 2 V with step of 80 mV."]
    #[inline(always)]
    pub fn usb_drefh(&self) -> USB_DREFH_R {
        USB_DREFH_R::new(((self.bits >> 21) & 3) as u8)
    }
    #[doc = "Bits 23:24 - Represents the single-end input threhold vrefl, 1.76 V to 2 V with step of 80 mV."]
    #[inline(always)]
    pub fn usb_drefl(&self) -> USB_DREFL_R {
        USB_DREFL_R::new(((self.bits >> 23) & 3) as u8)
    }
    #[doc = "Bit 25 - Represents whether the D+ and D- pins is exchanged. 1: exchanged. 0: not exchanged."]
    #[inline(always)]
    pub fn usb_exchg_pins(&self) -> USB_EXCHG_PINS_R {
        USB_EXCHG_PINS_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Represents whether vdd spi pin is functioned as gpio. 1: functioned. 0: not functioned."]
    #[inline(always)]
    pub fn vdd_spi_as_gpio(&self) -> VDD_SPI_AS_GPIO_R {
        VDD_SPI_AS_GPIO_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bits 27:28 - Reserved."]
    #[inline(always)]
    pub fn rpt4_reserved0_2(&self) -> RPT4_RESERVED0_2_R {
        RPT4_RESERVED0_2_R::new(((self.bits >> 27) & 3) as u8)
    }
    #[doc = "Bit 29 - Reserved."]
    #[inline(always)]
    pub fn rpt4_reserved0_1(&self) -> RPT4_RESERVED0_1_R {
        RPT4_RESERVED0_1_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bits 30:31 - Reserved."]
    #[inline(always)]
    pub fn rpt4_reserved0_0(&self) -> RPT4_RESERVED0_0_R {
        RPT4_RESERVED0_0_R::new(((self.bits >> 30) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_REPEAT_DATA0")
            .field("rd_dis", &self.rd_dis())
            .field("swap_uart_sdio_en", &self.swap_uart_sdio_en())
            .field("dis_icache", &self.dis_icache())
            .field("dis_usb_jtag", &self.dis_usb_jtag())
            .field("dis_download_icache", &self.dis_download_icache())
            .field("dis_usb_serial_jtag", &self.dis_usb_serial_jtag())
            .field("dis_force_download", &self.dis_force_download())
            .field("spi_download_mspi_dis", &self.spi_download_mspi_dis())
            .field("dis_can", &self.dis_can())
            .field("jtag_sel_enable", &self.jtag_sel_enable())
            .field("soft_dis_jtag", &self.soft_dis_jtag())
            .field("dis_pad_jtag", &self.dis_pad_jtag())
            .field(
                "dis_download_manual_encrypt",
                &self.dis_download_manual_encrypt(),
            )
            .field("usb_drefh", &self.usb_drefh())
            .field("usb_drefl", &self.usb_drefl())
            .field("usb_exchg_pins", &self.usb_exchg_pins())
            .field("vdd_spi_as_gpio", &self.vdd_spi_as_gpio())
            .field("rpt4_reserved0_2", &self.rpt4_reserved0_2())
            .field("rpt4_reserved0_1", &self.rpt4_reserved0_1())
            .field("rpt4_reserved0_0", &self.rpt4_reserved0_0())
            .finish()
    }
}
#[doc = "BLOCK0 data register 1.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_data0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_REPEAT_DATA0_SPEC;
impl crate::RegisterSpec for RD_REPEAT_DATA0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_repeat_data0::R`](R) reader structure"]
impl crate::Readable for RD_REPEAT_DATA0_SPEC {}
#[doc = "`reset()` method sets RD_REPEAT_DATA0 to value 0"]
impl crate::Resettable for RD_REPEAT_DATA0_SPEC {}
