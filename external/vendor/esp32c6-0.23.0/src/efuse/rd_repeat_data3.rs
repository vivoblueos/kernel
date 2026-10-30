#[doc = "Register `RD_REPEAT_DATA3` reader"]
pub type R = crate::R<RD_REPEAT_DATA3_SPEC>;
#[doc = "Field `DIS_DOWNLOAD_MODE` reader - Represents whether Download mode is disabled or enabled. 1: disabled. 0: enabled."]
pub type DIS_DOWNLOAD_MODE_R = crate::BitReader;
#[doc = "Field `DIS_DIRECT_BOOT` reader - Represents whether direct boot mode is disabled or enabled. 1: disabled. 0: enabled."]
pub type DIS_DIRECT_BOOT_R = crate::BitReader;
#[doc = "Field `DIS_USB_PRINT` reader - Represents whether print from USB-Serial-JTAG is disabled or enabled. 1: disabled. 0: enabled."]
pub type DIS_USB_PRINT_R = crate::BitReader;
#[doc = "Field `RPT4_RESERVED3_5` reader - Reserved."]
pub type RPT4_RESERVED3_5_R = crate::BitReader;
#[doc = "Field `DIS_USB_SERIAL_JTAG_DOWNLOAD_MODE` reader - Represents whether the USB-Serial-JTAG download function is disabled or enabled. 1: disabled. 0: enabled."]
pub type DIS_USB_SERIAL_JTAG_DOWNLOAD_MODE_R = crate::BitReader;
#[doc = "Field `ENABLE_SECURITY_DOWNLOAD` reader - Represents whether security download is enabled or disabled. 1: enabled. 0: disabled."]
pub type ENABLE_SECURITY_DOWNLOAD_R = crate::BitReader;
#[doc = "Field `UART_PRINT_CONTROL` reader - Represents the type of UART printing. 00: force enable printing. 01: enable printing when GPIO8 is reset at low level. 10: enable printing when GPIO8 is reset at high level. 11: force disable printing."]
pub type UART_PRINT_CONTROL_R = crate::FieldReader;
#[doc = "Field `RPT4_RESERVED3_4` reader - Reserved."]
pub type RPT4_RESERVED3_4_R = crate::BitReader;
#[doc = "Field `RPT4_RESERVED3_3` reader - Reserved."]
pub type RPT4_RESERVED3_3_R = crate::BitReader;
#[doc = "Field `RPT4_RESERVED3_2` reader - Reserved."]
pub type RPT4_RESERVED3_2_R = crate::FieldReader;
#[doc = "Field `RPT4_RESERVED3_1` reader - Reserved."]
pub type RPT4_RESERVED3_1_R = crate::BitReader;
#[doc = "Field `FORCE_SEND_RESUME` reader - Represents whether ROM code is forced to send a resume command during SPI boot. 1: forced. 0:not forced."]
pub type FORCE_SEND_RESUME_R = crate::BitReader;
#[doc = "Field `SECURE_VERSION` reader - Represents the version used by ESP-IDF anti-rollback feature."]
pub type SECURE_VERSION_R = crate::FieldReader<u16>;
#[doc = "Field `SECURE_BOOT_DISABLE_FAST_WAKE` reader - Represents whether FAST VERIFY ON WAKE is disabled or enabled when Secure Boot is enabled. 1: disabled. 0: enabled."]
pub type SECURE_BOOT_DISABLE_FAST_WAKE_R = crate::BitReader;
#[doc = "Field `RPT4_RESERVED3_0` reader - Reserved."]
pub type RPT4_RESERVED3_0_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Represents whether Download mode is disabled or enabled. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn dis_download_mode(&self) -> DIS_DOWNLOAD_MODE_R {
        DIS_DOWNLOAD_MODE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Represents whether direct boot mode is disabled or enabled. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn dis_direct_boot(&self) -> DIS_DIRECT_BOOT_R {
        DIS_DIRECT_BOOT_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Represents whether print from USB-Serial-JTAG is disabled or enabled. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn dis_usb_print(&self) -> DIS_USB_PRINT_R {
        DIS_USB_PRINT_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Reserved."]
    #[inline(always)]
    pub fn rpt4_reserved3_5(&self) -> RPT4_RESERVED3_5_R {
        RPT4_RESERVED3_5_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Represents whether the USB-Serial-JTAG download function is disabled or enabled. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn dis_usb_serial_jtag_download_mode(&self) -> DIS_USB_SERIAL_JTAG_DOWNLOAD_MODE_R {
        DIS_USB_SERIAL_JTAG_DOWNLOAD_MODE_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Represents whether security download is enabled or disabled. 1: enabled. 0: disabled."]
    #[inline(always)]
    pub fn enable_security_download(&self) -> ENABLE_SECURITY_DOWNLOAD_R {
        ENABLE_SECURITY_DOWNLOAD_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bits 6:7 - Represents the type of UART printing. 00: force enable printing. 01: enable printing when GPIO8 is reset at low level. 10: enable printing when GPIO8 is reset at high level. 11: force disable printing."]
    #[inline(always)]
    pub fn uart_print_control(&self) -> UART_PRINT_CONTROL_R {
        UART_PRINT_CONTROL_R::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bit 8 - Reserved."]
    #[inline(always)]
    pub fn rpt4_reserved3_4(&self) -> RPT4_RESERVED3_4_R {
        RPT4_RESERVED3_4_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Reserved."]
    #[inline(always)]
    pub fn rpt4_reserved3_3(&self) -> RPT4_RESERVED3_3_R {
        RPT4_RESERVED3_3_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bits 10:11 - Reserved."]
    #[inline(always)]
    pub fn rpt4_reserved3_2(&self) -> RPT4_RESERVED3_2_R {
        RPT4_RESERVED3_2_R::new(((self.bits >> 10) & 3) as u8)
    }
    #[doc = "Bit 12 - Reserved."]
    #[inline(always)]
    pub fn rpt4_reserved3_1(&self) -> RPT4_RESERVED3_1_R {
        RPT4_RESERVED3_1_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Represents whether ROM code is forced to send a resume command during SPI boot. 1: forced. 0:not forced."]
    #[inline(always)]
    pub fn force_send_resume(&self) -> FORCE_SEND_RESUME_R {
        FORCE_SEND_RESUME_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bits 14:29 - Represents the version used by ESP-IDF anti-rollback feature."]
    #[inline(always)]
    pub fn secure_version(&self) -> SECURE_VERSION_R {
        SECURE_VERSION_R::new(((self.bits >> 14) & 0xffff) as u16)
    }
    #[doc = "Bit 30 - Represents whether FAST VERIFY ON WAKE is disabled or enabled when Secure Boot is enabled. 1: disabled. 0: enabled."]
    #[inline(always)]
    pub fn secure_boot_disable_fast_wake(&self) -> SECURE_BOOT_DISABLE_FAST_WAKE_R {
        SECURE_BOOT_DISABLE_FAST_WAKE_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Reserved."]
    #[inline(always)]
    pub fn rpt4_reserved3_0(&self) -> RPT4_RESERVED3_0_R {
        RPT4_RESERVED3_0_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_REPEAT_DATA3")
            .field("dis_download_mode", &self.dis_download_mode())
            .field("dis_direct_boot", &self.dis_direct_boot())
            .field("dis_usb_print", &self.dis_usb_print())
            .field("rpt4_reserved3_5", &self.rpt4_reserved3_5())
            .field(
                "dis_usb_serial_jtag_download_mode",
                &self.dis_usb_serial_jtag_download_mode(),
            )
            .field("enable_security_download", &self.enable_security_download())
            .field("uart_print_control", &self.uart_print_control())
            .field("rpt4_reserved3_4", &self.rpt4_reserved3_4())
            .field("rpt4_reserved3_3", &self.rpt4_reserved3_3())
            .field("rpt4_reserved3_2", &self.rpt4_reserved3_2())
            .field("rpt4_reserved3_1", &self.rpt4_reserved3_1())
            .field("force_send_resume", &self.force_send_resume())
            .field("secure_version", &self.secure_version())
            .field(
                "secure_boot_disable_fast_wake",
                &self.secure_boot_disable_fast_wake(),
            )
            .field("rpt4_reserved3_0", &self.rpt4_reserved3_0())
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
