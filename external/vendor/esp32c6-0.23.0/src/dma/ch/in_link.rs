#[doc = "Register `IN_LINK` reader"]
pub type R = crate::R<IN_LINK_SPEC>;
#[doc = "Register `IN_LINK` writer"]
pub type W = crate::W<IN_LINK_SPEC>;
#[doc = "Field `INLINK_ADDR` reader - This register stores the 20 least significant bits of the first inlink descriptor's address."]
pub type INLINK_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `INLINK_ADDR` writer - This register stores the 20 least significant bits of the first inlink descriptor's address."]
pub type INLINK_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 20, u32>;
#[doc = "Field `INLINK_AUTO_RET` reader - Set this bit to return to current inlink descriptor's address when there are some errors in current receiving data."]
pub type INLINK_AUTO_RET_R = crate::BitReader;
#[doc = "Field `INLINK_AUTO_RET` writer - Set this bit to return to current inlink descriptor's address when there are some errors in current receiving data."]
pub type INLINK_AUTO_RET_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `INLINK_STOP` writer - Set this bit to stop dealing with the inlink descriptors."]
pub type INLINK_STOP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `INLINK_START` writer - Set this bit to start dealing with the inlink descriptors."]
pub type INLINK_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `INLINK_RESTART` writer - Set this bit to mount a new inlink descriptor."]
pub type INLINK_RESTART_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `INLINK_PARK` reader - 1: the inlink descriptor's FSM is in idle state. 0: the inlink descriptor's FSM is working."]
pub type INLINK_PARK_R = crate::BitReader;
impl R {
    #[doc = "Bits 0:19 - This register stores the 20 least significant bits of the first inlink descriptor's address."]
    #[inline(always)]
    pub fn inlink_addr(&self) -> INLINK_ADDR_R {
        INLINK_ADDR_R::new(self.bits & 0x000f_ffff)
    }
    #[doc = "Bit 20 - Set this bit to return to current inlink descriptor's address when there are some errors in current receiving data."]
    #[inline(always)]
    pub fn inlink_auto_ret(&self) -> INLINK_AUTO_RET_R {
        INLINK_AUTO_RET_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 24 - 1: the inlink descriptor's FSM is in idle state. 0: the inlink descriptor's FSM is working."]
    #[inline(always)]
    pub fn inlink_park(&self) -> INLINK_PARK_R {
        INLINK_PARK_R::new(((self.bits >> 24) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IN_LINK")
            .field("inlink_addr", &self.inlink_addr())
            .field("inlink_auto_ret", &self.inlink_auto_ret())
            .field("inlink_park", &self.inlink_park())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:19 - This register stores the 20 least significant bits of the first inlink descriptor's address."]
    #[inline(always)]
    pub fn inlink_addr(&mut self) -> INLINK_ADDR_W<'_, IN_LINK_SPEC> {
        INLINK_ADDR_W::new(self, 0)
    }
    #[doc = "Bit 20 - Set this bit to return to current inlink descriptor's address when there are some errors in current receiving data."]
    #[inline(always)]
    pub fn inlink_auto_ret(&mut self) -> INLINK_AUTO_RET_W<'_, IN_LINK_SPEC> {
        INLINK_AUTO_RET_W::new(self, 20)
    }
    #[doc = "Bit 21 - Set this bit to stop dealing with the inlink descriptors."]
    #[inline(always)]
    pub fn inlink_stop(&mut self) -> INLINK_STOP_W<'_, IN_LINK_SPEC> {
        INLINK_STOP_W::new(self, 21)
    }
    #[doc = "Bit 22 - Set this bit to start dealing with the inlink descriptors."]
    #[inline(always)]
    pub fn inlink_start(&mut self) -> INLINK_START_W<'_, IN_LINK_SPEC> {
        INLINK_START_W::new(self, 22)
    }
    #[doc = "Bit 23 - Set this bit to mount a new inlink descriptor."]
    #[inline(always)]
    pub fn inlink_restart(&mut self) -> INLINK_RESTART_W<'_, IN_LINK_SPEC> {
        INLINK_RESTART_W::new(self, 23)
    }
}
#[doc = "Link descriptor configure and control register of Rx channel 0\n\nYou can [`read`](crate::Reg::read) this register and get [`in_link::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`in_link::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IN_LINK_SPEC;
impl crate::RegisterSpec for IN_LINK_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`in_link::R`](R) reader structure"]
impl crate::Readable for IN_LINK_SPEC {}
#[doc = "`write(|w| ..)` method takes [`in_link::W`](W) writer structure"]
impl crate::Writable for IN_LINK_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IN_LINK to value 0x0110_0000"]
impl crate::Resettable for IN_LINK_SPEC {
    const RESET_VALUE: u32 = 0x0110_0000;
}
