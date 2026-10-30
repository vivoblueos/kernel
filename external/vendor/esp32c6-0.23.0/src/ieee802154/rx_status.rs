#[doc = "Register `RX_STATUS` reader"]
pub type R = crate::R<RX_STATUS_SPEC>;
#[doc = "Register `RX_STATUS` writer"]
pub type W = crate::W<RX_STATUS_SPEC>;
#[doc = "Field `FILTER_FAIL_STATUS` reader - "]
pub type FILTER_FAIL_STATUS_R = crate::FieldReader;
#[doc = "Field `FILTER_FAIL_STATUS` writer - "]
pub type FILTER_FAIL_STATUS_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `RX_ABORT_STATUS` reader - "]
pub type RX_ABORT_STATUS_R = crate::FieldReader;
#[doc = "Field `RX_ABORT_STATUS` writer - "]
pub type RX_ABORT_STATUS_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RX_STATE` reader - "]
pub type RX_STATE_R = crate::FieldReader;
#[doc = "Field `RX_STATE` writer - "]
pub type RX_STATE_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `PREAMBLE_MATCH` reader - "]
pub type PREAMBLE_MATCH_R = crate::BitReader;
#[doc = "Field `PREAMBLE_MATCH` writer - "]
pub type PREAMBLE_MATCH_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SFD_MATCH` reader - "]
pub type SFD_MATCH_R = crate::BitReader;
#[doc = "Field `SFD_MATCH` writer - "]
pub type SFD_MATCH_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn filter_fail_status(&self) -> FILTER_FAIL_STATUS_R {
        FILTER_FAIL_STATUS_R::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:8"]
    #[inline(always)]
    pub fn rx_abort_status(&self) -> RX_ABORT_STATUS_R {
        RX_ABORT_STATUS_R::new(((self.bits >> 4) & 0x1f) as u8)
    }
    #[doc = "Bits 16:18"]
    #[inline(always)]
    pub fn rx_state(&self) -> RX_STATE_R {
        RX_STATE_R::new(((self.bits >> 16) & 7) as u8)
    }
    #[doc = "Bit 20"]
    #[inline(always)]
    pub fn preamble_match(&self) -> PREAMBLE_MATCH_R {
        PREAMBLE_MATCH_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21"]
    #[inline(always)]
    pub fn sfd_match(&self) -> SFD_MATCH_R {
        SFD_MATCH_R::new(((self.bits >> 21) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RX_STATUS")
            .field("filter_fail_status", &self.filter_fail_status())
            .field("rx_abort_status", &self.rx_abort_status())
            .field("rx_state", &self.rx_state())
            .field("preamble_match", &self.preamble_match())
            .field("sfd_match", &self.sfd_match())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn filter_fail_status(&mut self) -> FILTER_FAIL_STATUS_W<'_, RX_STATUS_SPEC> {
        FILTER_FAIL_STATUS_W::new(self, 0)
    }
    #[doc = "Bits 4:8"]
    #[inline(always)]
    pub fn rx_abort_status(&mut self) -> RX_ABORT_STATUS_W<'_, RX_STATUS_SPEC> {
        RX_ABORT_STATUS_W::new(self, 4)
    }
    #[doc = "Bits 16:18"]
    #[inline(always)]
    pub fn rx_state(&mut self) -> RX_STATE_W<'_, RX_STATUS_SPEC> {
        RX_STATE_W::new(self, 16)
    }
    #[doc = "Bit 20"]
    #[inline(always)]
    pub fn preamble_match(&mut self) -> PREAMBLE_MATCH_W<'_, RX_STATUS_SPEC> {
        PREAMBLE_MATCH_W::new(self, 20)
    }
    #[doc = "Bit 21"]
    #[inline(always)]
    pub fn sfd_match(&mut self) -> SFD_MATCH_W<'_, RX_STATUS_SPEC> {
        SFD_MATCH_W::new(self, 21)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_status::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_status::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RX_STATUS_SPEC;
impl crate::RegisterSpec for RX_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rx_status::R`](R) reader structure"]
impl crate::Readable for RX_STATUS_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rx_status::W`](W) writer structure"]
impl crate::Writable for RX_STATUS_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RX_STATUS to value 0"]
impl crate::Resettable for RX_STATUS_SPEC {}
