#[doc = "Register `SLEEP_CONF1` reader"]
pub type R = crate::R<SLEEP_CONF1_SPEC>;
#[doc = "Register `SLEEP_CONF1` writer"]
pub type W = crate::W<SLEEP_CONF1_SPEC>;
#[doc = "Field `WK_CHAR0` reader - This register restores the specified char0 to wake up"]
pub type WK_CHAR0_R = crate::FieldReader;
#[doc = "Field `WK_CHAR0` writer - This register restores the specified char0 to wake up"]
pub type WK_CHAR0_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - This register restores the specified char0 to wake up"]
    #[inline(always)]
    pub fn wk_char0(&self) -> WK_CHAR0_R {
        WK_CHAR0_R::new((self.bits & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLEEP_CONF1")
            .field("wk_char0", &self.wk_char0())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - This register restores the specified char0 to wake up"]
    #[inline(always)]
    pub fn wk_char0(&mut self) -> WK_CHAR0_W<'_, SLEEP_CONF1_SPEC> {
        WK_CHAR0_W::new(self, 0)
    }
}
#[doc = "UART sleep configure register 1\n\nYou can [`read`](crate::Reg::read) this register and get [`sleep_conf1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sleep_conf1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLEEP_CONF1_SPEC;
impl crate::RegisterSpec for SLEEP_CONF1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sleep_conf1::R`](R) reader structure"]
impl crate::Readable for SLEEP_CONF1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sleep_conf1::W`](W) writer structure"]
impl crate::Writable for SLEEP_CONF1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLEEP_CONF1 to value 0"]
impl crate::Resettable for SLEEP_CONF1_SPEC {}
