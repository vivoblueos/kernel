#[doc = "Register `SLEEP_CONF0` reader"]
pub type R = crate::R<SLEEP_CONF0_SPEC>;
#[doc = "Register `SLEEP_CONF0` writer"]
pub type W = crate::W<SLEEP_CONF0_SPEC>;
#[doc = "Field `WK_CHAR1` reader - This register restores the specified wake up char1 to wake up"]
pub type WK_CHAR1_R = crate::FieldReader;
#[doc = "Field `WK_CHAR1` writer - This register restores the specified wake up char1 to wake up"]
pub type WK_CHAR1_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `WK_CHAR2` reader - This register restores the specified wake up char2 to wake up"]
pub type WK_CHAR2_R = crate::FieldReader;
#[doc = "Field `WK_CHAR2` writer - This register restores the specified wake up char2 to wake up"]
pub type WK_CHAR2_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `WK_CHAR3` reader - This register restores the specified wake up char3 to wake up"]
pub type WK_CHAR3_R = crate::FieldReader;
#[doc = "Field `WK_CHAR3` writer - This register restores the specified wake up char3 to wake up"]
pub type WK_CHAR3_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `WK_CHAR4` reader - This register restores the specified wake up char4 to wake up"]
pub type WK_CHAR4_R = crate::FieldReader;
#[doc = "Field `WK_CHAR4` writer - This register restores the specified wake up char4 to wake up"]
pub type WK_CHAR4_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - This register restores the specified wake up char1 to wake up"]
    #[inline(always)]
    pub fn wk_char1(&self) -> WK_CHAR1_R {
        WK_CHAR1_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - This register restores the specified wake up char2 to wake up"]
    #[inline(always)]
    pub fn wk_char2(&self) -> WK_CHAR2_R {
        WK_CHAR2_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - This register restores the specified wake up char3 to wake up"]
    #[inline(always)]
    pub fn wk_char3(&self) -> WK_CHAR3_R {
        WK_CHAR3_R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - This register restores the specified wake up char4 to wake up"]
    #[inline(always)]
    pub fn wk_char4(&self) -> WK_CHAR4_R {
        WK_CHAR4_R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLEEP_CONF0")
            .field("wk_char1", &self.wk_char1())
            .field("wk_char2", &self.wk_char2())
            .field("wk_char3", &self.wk_char3())
            .field("wk_char4", &self.wk_char4())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - This register restores the specified wake up char1 to wake up"]
    #[inline(always)]
    pub fn wk_char1(&mut self) -> WK_CHAR1_W<'_, SLEEP_CONF0_SPEC> {
        WK_CHAR1_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - This register restores the specified wake up char2 to wake up"]
    #[inline(always)]
    pub fn wk_char2(&mut self) -> WK_CHAR2_W<'_, SLEEP_CONF0_SPEC> {
        WK_CHAR2_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - This register restores the specified wake up char3 to wake up"]
    #[inline(always)]
    pub fn wk_char3(&mut self) -> WK_CHAR3_W<'_, SLEEP_CONF0_SPEC> {
        WK_CHAR3_W::new(self, 16)
    }
    #[doc = "Bits 24:31 - This register restores the specified wake up char4 to wake up"]
    #[inline(always)]
    pub fn wk_char4(&mut self) -> WK_CHAR4_W<'_, SLEEP_CONF0_SPEC> {
        WK_CHAR4_W::new(self, 24)
    }
}
#[doc = "UART sleep configure register 0\n\nYou can [`read`](crate::Reg::read) this register and get [`sleep_conf0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sleep_conf0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLEEP_CONF0_SPEC;
impl crate::RegisterSpec for SLEEP_CONF0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sleep_conf0::R`](R) reader structure"]
impl crate::Readable for SLEEP_CONF0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sleep_conf0::W`](W) writer structure"]
impl crate::Writable for SLEEP_CONF0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLEEP_CONF0 to value 0"]
impl crate::Resettable for SLEEP_CONF0_SPEC {}
