#[doc = "Register `LP_SLEEP_XTAL` reader"]
pub type R = crate::R<LP_SLEEP_XTAL_SPEC>;
#[doc = "Register `LP_SLEEP_XTAL` writer"]
pub type W = crate::W<LP_SLEEP_XTAL_SPEC>;
#[doc = "Field `LP_SLEEP_XPD_XTAL` reader - need_des"]
pub type LP_SLEEP_XPD_XTAL_R = crate::BitReader;
#[doc = "Field `LP_SLEEP_XPD_XTAL` writer - need_des"]
pub type LP_SLEEP_XPD_XTAL_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lp_sleep_xpd_xtal(&self) -> LP_SLEEP_XPD_XTAL_R {
        LP_SLEEP_XPD_XTAL_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LP_SLEEP_XTAL")
            .field("lp_sleep_xpd_xtal", &self.lp_sleep_xpd_xtal())
            .finish()
    }
}
impl W {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn lp_sleep_xpd_xtal(&mut self) -> LP_SLEEP_XPD_XTAL_W<'_, LP_SLEEP_XTAL_SPEC> {
        LP_SLEEP_XPD_XTAL_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`lp_sleep_xtal::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lp_sleep_xtal::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LP_SLEEP_XTAL_SPEC;
impl crate::RegisterSpec for LP_SLEEP_XTAL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lp_sleep_xtal::R`](R) reader structure"]
impl crate::Readable for LP_SLEEP_XTAL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`lp_sleep_xtal::W`](W) writer structure"]
impl crate::Writable for LP_SLEEP_XTAL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LP_SLEEP_XTAL to value 0x8000_0000"]
impl crate::Resettable for LP_SLEEP_XTAL_SPEC {
    const RESET_VALUE: u32 = 0x8000_0000;
}
