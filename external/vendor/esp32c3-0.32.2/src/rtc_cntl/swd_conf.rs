#[doc = "Register `SWD_CONF` reader"]
pub type R = crate::R<SWD_CONF_SPEC>;
#[doc = "Register `SWD_CONF` writer"]
pub type W = crate::W<SWD_CONF_SPEC>;
#[doc = "Field `SWD_RESET_FLAG` reader - swd reset flag"]
pub type SWD_RESET_FLAG_R = crate::BitReader;
#[doc = "Field `SWD_FEED_INT` reader - swd interrupt for feeding"]
pub type SWD_FEED_INT_R = crate::BitReader;
#[doc = "Field `SWD_BYPASS_RST` reader - Bypass swd rst"]
pub type SWD_BYPASS_RST_R = crate::BitReader;
#[doc = "Field `SWD_BYPASS_RST` writer - Bypass swd rst"]
pub type SWD_BYPASS_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SWD_SIGNAL_WIDTH` reader - adjust signal width send to swd"]
pub type SWD_SIGNAL_WIDTH_R = crate::FieldReader<u16>;
#[doc = "Field `SWD_SIGNAL_WIDTH` writer - adjust signal width send to swd"]
pub type SWD_SIGNAL_WIDTH_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `SWD_RST_FLAG_CLR` writer - reset swd reset flag"]
pub type SWD_RST_FLAG_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SWD_FEED` writer - Sw feed swd"]
pub type SWD_FEED_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SWD_DISABLE` reader - disabel SWD"]
pub type SWD_DISABLE_R = crate::BitReader;
#[doc = "Field `SWD_DISABLE` writer - disabel SWD"]
pub type SWD_DISABLE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SWD_AUTO_FEED_EN` reader - automatically feed swd when int comes"]
pub type SWD_AUTO_FEED_EN_R = crate::BitReader;
#[doc = "Field `SWD_AUTO_FEED_EN` writer - automatically feed swd when int comes"]
pub type SWD_AUTO_FEED_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - swd reset flag"]
    #[inline(always)]
    pub fn swd_reset_flag(&self) -> SWD_RESET_FLAG_R {
        SWD_RESET_FLAG_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - swd interrupt for feeding"]
    #[inline(always)]
    pub fn swd_feed_int(&self) -> SWD_FEED_INT_R {
        SWD_FEED_INT_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 17 - Bypass swd rst"]
    #[inline(always)]
    pub fn swd_bypass_rst(&self) -> SWD_BYPASS_RST_R {
        SWD_BYPASS_RST_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bits 18:27 - adjust signal width send to swd"]
    #[inline(always)]
    pub fn swd_signal_width(&self) -> SWD_SIGNAL_WIDTH_R {
        SWD_SIGNAL_WIDTH_R::new(((self.bits >> 18) & 0x03ff) as u16)
    }
    #[doc = "Bit 30 - disabel SWD"]
    #[inline(always)]
    pub fn swd_disable(&self) -> SWD_DISABLE_R {
        SWD_DISABLE_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - automatically feed swd when int comes"]
    #[inline(always)]
    pub fn swd_auto_feed_en(&self) -> SWD_AUTO_FEED_EN_R {
        SWD_AUTO_FEED_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SWD_CONF")
            .field("swd_reset_flag", &self.swd_reset_flag())
            .field("swd_feed_int", &self.swd_feed_int())
            .field("swd_bypass_rst", &self.swd_bypass_rst())
            .field("swd_signal_width", &self.swd_signal_width())
            .field("swd_disable", &self.swd_disable())
            .field("swd_auto_feed_en", &self.swd_auto_feed_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 17 - Bypass swd rst"]
    #[inline(always)]
    pub fn swd_bypass_rst(&mut self) -> SWD_BYPASS_RST_W<'_, SWD_CONF_SPEC> {
        SWD_BYPASS_RST_W::new(self, 17)
    }
    #[doc = "Bits 18:27 - adjust signal width send to swd"]
    #[inline(always)]
    pub fn swd_signal_width(&mut self) -> SWD_SIGNAL_WIDTH_W<'_, SWD_CONF_SPEC> {
        SWD_SIGNAL_WIDTH_W::new(self, 18)
    }
    #[doc = "Bit 28 - reset swd reset flag"]
    #[inline(always)]
    pub fn swd_rst_flag_clr(&mut self) -> SWD_RST_FLAG_CLR_W<'_, SWD_CONF_SPEC> {
        SWD_RST_FLAG_CLR_W::new(self, 28)
    }
    #[doc = "Bit 29 - Sw feed swd"]
    #[inline(always)]
    pub fn swd_feed(&mut self) -> SWD_FEED_W<'_, SWD_CONF_SPEC> {
        SWD_FEED_W::new(self, 29)
    }
    #[doc = "Bit 30 - disabel SWD"]
    #[inline(always)]
    pub fn swd_disable(&mut self) -> SWD_DISABLE_W<'_, SWD_CONF_SPEC> {
        SWD_DISABLE_W::new(self, 30)
    }
    #[doc = "Bit 31 - automatically feed swd when int comes"]
    #[inline(always)]
    pub fn swd_auto_feed_en(&mut self) -> SWD_AUTO_FEED_EN_W<'_, SWD_CONF_SPEC> {
        SWD_AUTO_FEED_EN_W::new(self, 31)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`swd_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`swd_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SWD_CONF_SPEC;
impl crate::RegisterSpec for SWD_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`swd_conf::R`](R) reader structure"]
impl crate::Readable for SWD_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`swd_conf::W`](W) writer structure"]
impl crate::Writable for SWD_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SWD_CONF to value 0x04b0_0000"]
impl crate::Resettable for SWD_CONF_SPEC {
    const RESET_VALUE: u32 = 0x04b0_0000;
}
