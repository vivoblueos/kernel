#[doc = "Register `RD_REPEAT_DATA3` reader"]
pub type R = crate::R<RD_REPEAT_DATA3_SPEC>;
#[doc = "Field `DIS_DOWNLOAD_MODE` reader - Set this bit to disable download mode (boot_mode\\[3:0\\] = 0, 1, 2, 3, 6, 7)."]
pub type DIS_DOWNLOAD_MODE_R = crate::BitReader;
#[doc = "Field `DIS_LEGACY_SPI_BOOT` reader - Set this bit to disable Legacy SPI boot mode (boot_mode\\[3:0\\] = 4)."]
pub type DIS_LEGACY_SPI_BOOT_R = crate::BitReader;
#[doc = "Field `UART_PRINT_CHANNEL` reader - Selectes the default UART print channel. 0: UART0. 1: UART1."]
pub type UART_PRINT_CHANNEL_R = crate::BitReader;
#[doc = "Field `FLASH_ECC_MODE` reader - Set ECC mode in ROM, 0: ROM would Enable Flash ECC 16to18 byte mode. 1:ROM would use 16to17 byte mode."]
pub type FLASH_ECC_MODE_R = crate::BitReader;
#[doc = "Field `DIS_USB_DOWNLOAD_MODE` reader - Set this bit to disable UART download mode through USB."]
pub type DIS_USB_DOWNLOAD_MODE_R = crate::BitReader;
#[doc = "Field `ENABLE_SECURITY_DOWNLOAD` reader - Set this bit to enable secure UART download mode."]
pub type ENABLE_SECURITY_DOWNLOAD_R = crate::BitReader;
#[doc = "Field `UART_PRINT_CONTROL` reader - Set the default UARTboot message output mode. 00: Enabled. 01: Enabled when GPIO8 is low at reset. 10: Enabled when GPIO8 is high at reset. 11:disabled."]
pub type UART_PRINT_CONTROL_R = crate::FieldReader;
#[doc = "Field `PIN_POWER_SELECTION` reader - GPIO33-GPIO37 power supply selection in ROM code. 0: VDD3P3_CPU. 1: VDD_SPI."]
pub type PIN_POWER_SELECTION_R = crate::BitReader;
#[doc = "Field `FLASH_TYPE` reader - Set the maximum lines of SPI flash. 0: four lines. 1: eight lines."]
pub type FLASH_TYPE_R = crate::BitReader;
#[doc = "Field `FLASH_PAGE_SIZE` reader - Set Flash page size."]
pub type FLASH_PAGE_SIZE_R = crate::FieldReader;
#[doc = "Field `FLASH_ECC_EN` reader - Set 1 to enable ECC for flash boot."]
pub type FLASH_ECC_EN_R = crate::BitReader;
#[doc = "Field `FORCE_SEND_RESUME` reader - Set this bit to force ROM code to send a resume command during SPI boot."]
pub type FORCE_SEND_RESUME_R = crate::BitReader;
#[doc = "Field `SECURE_VERSION` reader - Secure version (used by ESP-IDF anti-rollback feature)."]
pub type SECURE_VERSION_R = crate::FieldReader<u16>;
#[doc = "Field `RPT4_RESERVED1` reader - Reserved (used for four backups method)."]
pub type RPT4_RESERVED1_R = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - Set this bit to disable download mode (boot_mode\\[3:0\\] = 0, 1, 2, 3, 6, 7)."]
    #[inline(always)]
    pub fn dis_download_mode(&self) -> DIS_DOWNLOAD_MODE_R {
        DIS_DOWNLOAD_MODE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Set this bit to disable Legacy SPI boot mode (boot_mode\\[3:0\\] = 4)."]
    #[inline(always)]
    pub fn dis_legacy_spi_boot(&self) -> DIS_LEGACY_SPI_BOOT_R {
        DIS_LEGACY_SPI_BOOT_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Selectes the default UART print channel. 0: UART0. 1: UART1."]
    #[inline(always)]
    pub fn uart_print_channel(&self) -> UART_PRINT_CHANNEL_R {
        UART_PRINT_CHANNEL_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Set ECC mode in ROM, 0: ROM would Enable Flash ECC 16to18 byte mode. 1:ROM would use 16to17 byte mode."]
    #[inline(always)]
    pub fn flash_ecc_mode(&self) -> FLASH_ECC_MODE_R {
        FLASH_ECC_MODE_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Set this bit to disable UART download mode through USB."]
    #[inline(always)]
    pub fn dis_usb_download_mode(&self) -> DIS_USB_DOWNLOAD_MODE_R {
        DIS_USB_DOWNLOAD_MODE_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Set this bit to enable secure UART download mode."]
    #[inline(always)]
    pub fn enable_security_download(&self) -> ENABLE_SECURITY_DOWNLOAD_R {
        ENABLE_SECURITY_DOWNLOAD_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bits 6:7 - Set the default UARTboot message output mode. 00: Enabled. 01: Enabled when GPIO8 is low at reset. 10: Enabled when GPIO8 is high at reset. 11:disabled."]
    #[inline(always)]
    pub fn uart_print_control(&self) -> UART_PRINT_CONTROL_R {
        UART_PRINT_CONTROL_R::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bit 8 - GPIO33-GPIO37 power supply selection in ROM code. 0: VDD3P3_CPU. 1: VDD_SPI."]
    #[inline(always)]
    pub fn pin_power_selection(&self) -> PIN_POWER_SELECTION_R {
        PIN_POWER_SELECTION_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Set the maximum lines of SPI flash. 0: four lines. 1: eight lines."]
    #[inline(always)]
    pub fn flash_type(&self) -> FLASH_TYPE_R {
        FLASH_TYPE_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bits 10:11 - Set Flash page size."]
    #[inline(always)]
    pub fn flash_page_size(&self) -> FLASH_PAGE_SIZE_R {
        FLASH_PAGE_SIZE_R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bit 12 - Set 1 to enable ECC for flash boot."]
    #[inline(always)]
    pub fn flash_ecc_en(&self) -> FLASH_ECC_EN_R {
        FLASH_ECC_EN_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Set this bit to force ROM code to send a resume command during SPI boot."]
    #[inline(always)]
    pub fn force_send_resume(&self) -> FORCE_SEND_RESUME_R {
        FORCE_SEND_RESUME_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bits 14:29 - Secure version (used by ESP-IDF anti-rollback feature)."]
    #[inline(always)]
    pub fn secure_version(&self) -> SECURE_VERSION_R {
        SECURE_VERSION_R::new(((self.bits >> 14) & 0xffff) as u16)
    }
    #[doc = "Bits 30:31 - Reserved (used for four backups method)."]
    #[inline(always)]
    pub fn rpt4_reserved1(&self) -> RPT4_RESERVED1_R {
        RPT4_RESERVED1_R::new(((self.bits >> 30) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_REPEAT_DATA3")
            .field("dis_download_mode", &self.dis_download_mode())
            .field("dis_legacy_spi_boot", &self.dis_legacy_spi_boot())
            .field("uart_print_channel", &self.uart_print_channel())
            .field("flash_ecc_mode", &self.flash_ecc_mode())
            .field("dis_usb_download_mode", &self.dis_usb_download_mode())
            .field("enable_security_download", &self.enable_security_download())
            .field("uart_print_control", &self.uart_print_control())
            .field("pin_power_selection", &self.pin_power_selection())
            .field("flash_type", &self.flash_type())
            .field("flash_page_size", &self.flash_page_size())
            .field("flash_ecc_en", &self.flash_ecc_en())
            .field("force_send_resume", &self.force_send_resume())
            .field("secure_version", &self.secure_version())
            .field("rpt4_reserved1", &self.rpt4_reserved1())
            .finish()
    }
}
#[doc = "BLOCK0 data register 4.\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_repeat_data3::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_REPEAT_DATA3_SPEC;
impl crate::RegisterSpec for RD_REPEAT_DATA3_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_repeat_data3::R`](R) reader structure"]
impl crate::Readable for RD_REPEAT_DATA3_SPEC {}
#[doc = "`reset()` method sets RD_REPEAT_DATA3 to value 0"]
impl crate::Resettable for RD_REPEAT_DATA3_SPEC {}
