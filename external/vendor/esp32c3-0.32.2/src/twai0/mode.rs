#[doc = "Register `MODE` reader"]
pub type R = crate::R<MODE_SPEC>;
#[doc = "Register `MODE` writer"]
pub type W = crate::W<MODE_SPEC>;
#[doc = "Field `RESET_MODE` reader - This bit is used to configure the operating mode of the TWAI Controller. 1: Reset mode; 0: Operating mode."]
pub type RESET_MODE_R = crate::BitReader;
#[doc = "Field `RESET_MODE` writer - This bit is used to configure the operating mode of the TWAI Controller. 1: Reset mode; 0: Operating mode."]
pub type RESET_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LISTEN_ONLY_MODE` reader - 1: Listen only mode. In this mode the nodes will only receive messages from the bus, without generating the acknowledge signal nor updating the RX error counter."]
pub type LISTEN_ONLY_MODE_R = crate::BitReader;
#[doc = "Field `LISTEN_ONLY_MODE` writer - 1: Listen only mode. In this mode the nodes will only receive messages from the bus, without generating the acknowledge signal nor updating the RX error counter."]
pub type LISTEN_ONLY_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SELF_TEST_MODE` reader - 1: Self test mode. In this mode the TX nodes can perform a successful transmission without receiving the acknowledge signal. This mode is often used to test a single node with the self reception request command."]
pub type SELF_TEST_MODE_R = crate::BitReader;
#[doc = "Field `SELF_TEST_MODE` writer - 1: Self test mode. In this mode the TX nodes can perform a successful transmission without receiving the acknowledge signal. This mode is often used to test a single node with the self reception request command."]
pub type SELF_TEST_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RX_FILTER_MODE` reader - This bit is used to configure the filter mode. 0: Dual filter mode; 1: Single filter mode."]
pub type RX_FILTER_MODE_R = crate::BitReader;
#[doc = "Field `RX_FILTER_MODE` writer - This bit is used to configure the filter mode. 0: Dual filter mode; 1: Single filter mode."]
pub type RX_FILTER_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - This bit is used to configure the operating mode of the TWAI Controller. 1: Reset mode; 0: Operating mode."]
    #[inline(always)]
    pub fn reset_mode(&self) -> RESET_MODE_R {
        RESET_MODE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - 1: Listen only mode. In this mode the nodes will only receive messages from the bus, without generating the acknowledge signal nor updating the RX error counter."]
    #[inline(always)]
    pub fn listen_only_mode(&self) -> LISTEN_ONLY_MODE_R {
        LISTEN_ONLY_MODE_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - 1: Self test mode. In this mode the TX nodes can perform a successful transmission without receiving the acknowledge signal. This mode is often used to test a single node with the self reception request command."]
    #[inline(always)]
    pub fn self_test_mode(&self) -> SELF_TEST_MODE_R {
        SELF_TEST_MODE_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - This bit is used to configure the filter mode. 0: Dual filter mode; 1: Single filter mode."]
    #[inline(always)]
    pub fn rx_filter_mode(&self) -> RX_FILTER_MODE_R {
        RX_FILTER_MODE_R::new(((self.bits >> 3) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MODE")
            .field("reset_mode", &self.reset_mode())
            .field("listen_only_mode", &self.listen_only_mode())
            .field("self_test_mode", &self.self_test_mode())
            .field("rx_filter_mode", &self.rx_filter_mode())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - This bit is used to configure the operating mode of the TWAI Controller. 1: Reset mode; 0: Operating mode."]
    #[inline(always)]
    pub fn reset_mode(&mut self) -> RESET_MODE_W<'_, MODE_SPEC> {
        RESET_MODE_W::new(self, 0)
    }
    #[doc = "Bit 1 - 1: Listen only mode. In this mode the nodes will only receive messages from the bus, without generating the acknowledge signal nor updating the RX error counter."]
    #[inline(always)]
    pub fn listen_only_mode(&mut self) -> LISTEN_ONLY_MODE_W<'_, MODE_SPEC> {
        LISTEN_ONLY_MODE_W::new(self, 1)
    }
    #[doc = "Bit 2 - 1: Self test mode. In this mode the TX nodes can perform a successful transmission without receiving the acknowledge signal. This mode is often used to test a single node with the self reception request command."]
    #[inline(always)]
    pub fn self_test_mode(&mut self) -> SELF_TEST_MODE_W<'_, MODE_SPEC> {
        SELF_TEST_MODE_W::new(self, 2)
    }
    #[doc = "Bit 3 - This bit is used to configure the filter mode. 0: Dual filter mode; 1: Single filter mode."]
    #[inline(always)]
    pub fn rx_filter_mode(&mut self) -> RX_FILTER_MODE_W<'_, MODE_SPEC> {
        RX_FILTER_MODE_W::new(self, 3)
    }
}
#[doc = "Mode Register\n\nYou can [`read`](crate::Reg::read) this register and get [`mode::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mode::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MODE_SPEC;
impl crate::RegisterSpec for MODE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mode::R`](R) reader structure"]
impl crate::Readable for MODE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mode::W`](W) writer structure"]
impl crate::Writable for MODE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MODE to value 0x01"]
impl crate::Resettable for MODE_SPEC {
    const RESET_VALUE: u32 = 0x01;
}
