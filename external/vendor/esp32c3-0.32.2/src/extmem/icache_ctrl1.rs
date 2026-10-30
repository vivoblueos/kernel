#[doc = "Register `ICACHE_CTRL1` reader"]
pub type R = crate::R<ICACHE_CTRL1_SPEC>;
#[doc = "Register `ICACHE_CTRL1` writer"]
pub type W = crate::W<ICACHE_CTRL1_SPEC>;
#[doc = "Field `ICACHE_SHUT_IBUS` reader - The bit is used to disable core0 ibus, 0: enable, 1: disable"]
pub type ICACHE_SHUT_IBUS_R = crate::BitReader;
#[doc = "Field `ICACHE_SHUT_IBUS` writer - The bit is used to disable core0 ibus, 0: enable, 1: disable"]
pub type ICACHE_SHUT_IBUS_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ICACHE_SHUT_DBUS` reader - The bit is used to disable core1 ibus, 0: enable, 1: disable"]
pub type ICACHE_SHUT_DBUS_R = crate::BitReader;
#[doc = "Field `ICACHE_SHUT_DBUS` writer - The bit is used to disable core1 ibus, 0: enable, 1: disable"]
pub type ICACHE_SHUT_DBUS_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The bit is used to disable core0 ibus, 0: enable, 1: disable"]
    #[inline(always)]
    pub fn icache_shut_ibus(&self) -> ICACHE_SHUT_IBUS_R {
        ICACHE_SHUT_IBUS_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to disable core1 ibus, 0: enable, 1: disable"]
    #[inline(always)]
    pub fn icache_shut_dbus(&self) -> ICACHE_SHUT_DBUS_R {
        ICACHE_SHUT_DBUS_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ICACHE_CTRL1")
            .field("icache_shut_ibus", &self.icache_shut_ibus())
            .field("icache_shut_dbus", &self.icache_shut_dbus())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to disable core0 ibus, 0: enable, 1: disable"]
    #[inline(always)]
    pub fn icache_shut_ibus(&mut self) -> ICACHE_SHUT_IBUS_W<'_, ICACHE_CTRL1_SPEC> {
        ICACHE_SHUT_IBUS_W::new(self, 0)
    }
    #[doc = "Bit 1 - The bit is used to disable core1 ibus, 0: enable, 1: disable"]
    #[inline(always)]
    pub fn icache_shut_dbus(&mut self) -> ICACHE_SHUT_DBUS_W<'_, ICACHE_CTRL1_SPEC> {
        ICACHE_SHUT_DBUS_W::new(self, 1)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`icache_ctrl1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`icache_ctrl1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ICACHE_CTRL1_SPEC;
impl crate::RegisterSpec for ICACHE_CTRL1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`icache_ctrl1::R`](R) reader structure"]
impl crate::Readable for ICACHE_CTRL1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`icache_ctrl1::W`](W) writer structure"]
impl crate::Writable for ICACHE_CTRL1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ICACHE_CTRL1 to value 0x03"]
impl crate::Resettable for ICACHE_CTRL1_SPEC {
    const RESET_VALUE: u32 = 0x03;
}
