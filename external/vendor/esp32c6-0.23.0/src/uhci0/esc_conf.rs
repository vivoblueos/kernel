#[doc = "Register `ESC_CONF%s` reader"]
pub type R = crate::R<ESC_CONF_SPEC>;
#[doc = "Register `ESC_CONF%s` writer"]
pub type W = crate::W<ESC_CONF_SPEC>;
#[doc = "Field `SEPER_CHAR` reader - Configures the delimiter for encoding, default value is 0xC0."]
pub type SEPER_CHAR_R = crate::FieldReader;
#[doc = "Field `SEPER_CHAR` writer - Configures the delimiter for encoding, default value is 0xC0."]
pub type SEPER_CHAR_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SEPER_ESC_CHAR0` reader - Configures the first char of SLIP escape character, default value is 0xDB."]
pub type SEPER_ESC_CHAR0_R = crate::FieldReader;
#[doc = "Field `SEPER_ESC_CHAR0` writer - Configures the first char of SLIP escape character, default value is 0xDB."]
pub type SEPER_ESC_CHAR0_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SEPER_ESC_CHAR1` reader - Configures the second char of SLIP escape character, default value is 0xDC."]
pub type SEPER_ESC_CHAR1_R = crate::FieldReader;
#[doc = "Field `SEPER_ESC_CHAR1` writer - Configures the second char of SLIP escape character, default value is 0xDC."]
pub type SEPER_ESC_CHAR1_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - Configures the delimiter for encoding, default value is 0xC0."]
    #[inline(always)]
    pub fn seper_char(&self) -> SEPER_CHAR_R {
        SEPER_CHAR_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - Configures the first char of SLIP escape character, default value is 0xDB."]
    #[inline(always)]
    pub fn seper_esc_char0(&self) -> SEPER_ESC_CHAR0_R {
        SEPER_ESC_CHAR0_R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - Configures the second char of SLIP escape character, default value is 0xDC."]
    #[inline(always)]
    pub fn seper_esc_char1(&self) -> SEPER_ESC_CHAR1_R {
        SEPER_ESC_CHAR1_R::new(((self.bits >> 16) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ESC_CONF")
            .field("seper_char", &self.seper_char())
            .field("seper_esc_char0", &self.seper_esc_char0())
            .field("seper_esc_char1", &self.seper_esc_char1())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - Configures the delimiter for encoding, default value is 0xC0."]
    #[inline(always)]
    pub fn seper_char(&mut self) -> SEPER_CHAR_W<'_, ESC_CONF_SPEC> {
        SEPER_CHAR_W::new(self, 0)
    }
    #[doc = "Bits 8:15 - Configures the first char of SLIP escape character, default value is 0xDB."]
    #[inline(always)]
    pub fn seper_esc_char0(&mut self) -> SEPER_ESC_CHAR0_W<'_, ESC_CONF_SPEC> {
        SEPER_ESC_CHAR0_W::new(self, 8)
    }
    #[doc = "Bits 16:23 - Configures the second char of SLIP escape character, default value is 0xDC."]
    #[inline(always)]
    pub fn seper_esc_char1(&mut self) -> SEPER_ESC_CHAR1_W<'_, ESC_CONF_SPEC> {
        SEPER_ESC_CHAR1_W::new(self, 16)
    }
}
#[doc = "UHCI Escapes Sequence Configuration Register%s\n\nYou can [`read`](crate::Reg::read) this register and get [`esc_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`esc_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ESC_CONF_SPEC;
impl crate::RegisterSpec for ESC_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`esc_conf::R`](R) reader structure"]
impl crate::Readable for ESC_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`esc_conf::W`](W) writer structure"]
impl crate::Writable for ESC_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ESC_CONF%s to value 0x00dc_dbc0"]
impl crate::Resettable for ESC_CONF_SPEC {
    const RESET_VALUE: u32 = 0x00dc_dbc0;
}
