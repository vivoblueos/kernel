#[doc = "Register `USB` reader"]
pub type R = crate::R<USB_SPEC>;
#[doc = "Register `USB` writer"]
pub type W = crate::W<USB_SPEC>;
#[doc = "Field `RESET_DISABLE` reader - need_des"]
pub type RESET_DISABLE_R = crate::BitReader;
#[doc = "Field `RESET_DISABLE` writer - need_des"]
pub type RESET_DISABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn reset_disable(&self) -> RESET_DISABLE_R {
        RESET_DISABLE_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("USB")
            .field("reset_disable", &self.reset_disable())
            .finish()
    }
}
impl W {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn reset_disable(&mut self) -> RESET_DISABLE_W<'_, USB_SPEC> {
        RESET_DISABLE_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`usb::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`usb::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct USB_SPEC;
impl crate::RegisterSpec for USB_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`usb::R`](R) reader structure"]
impl crate::Readable for USB_SPEC {}
#[doc = "`write(|w| ..)` method takes [`usb::W`](W) writer structure"]
impl crate::Writable for USB_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets USB to value 0"]
impl crate::Resettable for USB_SPEC {}
