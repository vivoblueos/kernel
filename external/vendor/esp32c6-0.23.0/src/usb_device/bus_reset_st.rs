#[doc = "Register `BUS_RESET_ST` reader"]
pub type R = crate::R<BUS_RESET_ST_SPEC>;
#[doc = "Field `USB_BUS_RESET_ST` reader - USB bus reset status. 0: USB-Serial-JTAG is in usb bus reset status. 1: USB bus reset is released."]
pub type USB_BUS_RESET_ST_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - USB bus reset status. 0: USB-Serial-JTAG is in usb bus reset status. 1: USB bus reset is released."]
    #[inline(always)]
    pub fn usb_bus_reset_st(&self) -> USB_BUS_RESET_ST_R {
        USB_BUS_RESET_ST_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BUS_RESET_ST")
            .field("usb_bus_reset_st", &self.usb_bus_reset_st())
            .finish()
    }
}
#[doc = "USB Bus reset status register\n\nYou can [`read`](crate::Reg::read) this register and get [`bus_reset_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BUS_RESET_ST_SPEC;
impl crate::RegisterSpec for BUS_RESET_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`bus_reset_st::R`](R) reader structure"]
impl crate::Readable for BUS_RESET_ST_SPEC {}
#[doc = "`reset()` method sets BUS_RESET_ST to value 0x01"]
impl crate::Resettable for BUS_RESET_ST_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
