#[doc = "Register `CHIP_RST` reader"]
pub type R = crate::R<CHIP_RST_SPEC>;
#[doc = "Register `CHIP_RST` writer"]
pub type W = crate::W<CHIP_RST_SPEC>;
#[doc = "Field `RTS` reader - 1: Chip reset is detected from usb serial channel. Software write 1 to clear it."]
pub type RTS_R = crate::BitReader;
#[doc = "Field `DTR` reader - 1: Chip reset is detected from usb jtag channel. Software write 1 to clear it."]
pub type DTR_R = crate::BitReader;
#[doc = "Field `USB_UART_CHIP_RST_DIS` reader - Set this bit to disable chip reset from usb serial channel to reset chip."]
pub type USB_UART_CHIP_RST_DIS_R = crate::BitReader;
#[doc = "Field `USB_UART_CHIP_RST_DIS` writer - Set this bit to disable chip reset from usb serial channel to reset chip."]
pub type USB_UART_CHIP_RST_DIS_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - 1: Chip reset is detected from usb serial channel. Software write 1 to clear it."]
    #[inline(always)]
    pub fn rts(&self) -> RTS_R {
        RTS_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - 1: Chip reset is detected from usb jtag channel. Software write 1 to clear it."]
    #[inline(always)]
    pub fn dtr(&self) -> DTR_R {
        DTR_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set this bit to disable chip reset from usb serial channel to reset chip."]
    #[inline(always)]
    pub fn usb_uart_chip_rst_dis(&self) -> USB_UART_CHIP_RST_DIS_R {
        USB_UART_CHIP_RST_DIS_R::new(((self.bits >> 2) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CHIP_RST")
            .field("rts", &self.rts())
            .field("dtr", &self.dtr())
            .field("usb_uart_chip_rst_dis", &self.usb_uart_chip_rst_dis())
            .finish()
    }
}
impl W {
    #[doc = "Bit 2 - Set this bit to disable chip reset from usb serial channel to reset chip."]
    #[inline(always)]
    pub fn usb_uart_chip_rst_dis(&mut self) -> USB_UART_CHIP_RST_DIS_W<'_, CHIP_RST_SPEC> {
        USB_UART_CHIP_RST_DIS_W::new(self, 2)
    }
}
#[doc = "CDC-ACM chip reset control.\n\nYou can [`read`](crate::Reg::read) this register and get [`chip_rst::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`chip_rst::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CHIP_RST_SPEC;
impl crate::RegisterSpec for CHIP_RST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`chip_rst::R`](R) reader structure"]
impl crate::Readable for CHIP_RST_SPEC {}
#[doc = "`write(|w| ..)` method takes [`chip_rst::W`](W) writer structure"]
impl crate::Writable for CHIP_RST_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CHIP_RST to value 0"]
impl crate::Resettable for CHIP_RST_SPEC {}
