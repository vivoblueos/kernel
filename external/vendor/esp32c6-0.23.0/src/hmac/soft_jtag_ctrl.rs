#[doc = "Register `SOFT_JTAG_CTRL` writer"]
pub type W = crate::W<SOFT_JTAG_CTRL_SPEC>;
#[doc = "Field `SOFT_JTAG_CTRL` writer - Turn on JTAG verification."]
pub type SOFT_JTAG_CTRL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SOFT_JTAG_CTRL_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Turn on JTAG verification."]
    #[inline(always)]
    pub fn soft_jtag_ctrl(&mut self) -> SOFT_JTAG_CTRL_W<'_, SOFT_JTAG_CTRL_SPEC> {
        SOFT_JTAG_CTRL_W::new(self, 0)
    }
}
#[doc = "Jtag register 0.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`soft_jtag_ctrl::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SOFT_JTAG_CTRL_SPEC;
impl crate::RegisterSpec for SOFT_JTAG_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`soft_jtag_ctrl::W`](W) writer structure"]
impl crate::Writable for SOFT_JTAG_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SOFT_JTAG_CTRL to value 0"]
impl crate::Resettable for SOFT_JTAG_CTRL_SPEC {}
