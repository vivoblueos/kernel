#[doc = "Register `CONFIG` reader"]
pub type R = crate::R<CONFIG_SPEC>;
#[doc = "Register `CONFIG` writer"]
pub type W = crate::W<CONFIG_SPEC>;
#[doc = "Field `USE_XTAL` reader - reg_t0_use_xtal."]
pub type USE_XTAL_R = crate::BitReader;
#[doc = "Field `USE_XTAL` writer - reg_t0_use_xtal."]
pub type USE_XTAL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ALARM_EN` reader - reg_t0_alarm_en."]
pub type ALARM_EN_R = crate::BitReader;
#[doc = "Field `ALARM_EN` writer - reg_t0_alarm_en."]
pub type ALARM_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DIVCNT_RST` writer - reg_t0_divcnt_rst."]
pub type DIVCNT_RST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DIVIDER` reader - reg_t0_divider."]
pub type DIVIDER_R = crate::FieldReader<u16>;
#[doc = "Field `DIVIDER` writer - reg_t0_divider."]
pub type DIVIDER_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `AUTORELOAD` reader - reg_t0_autoreload."]
pub type AUTORELOAD_R = crate::BitReader;
#[doc = "Field `AUTORELOAD` writer - reg_t0_autoreload."]
pub type AUTORELOAD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `INCREASE` reader - reg_t0_increase."]
pub type INCREASE_R = crate::BitReader;
#[doc = "Field `INCREASE` writer - reg_t0_increase."]
pub type INCREASE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EN` reader - reg_t0_en."]
pub type EN_R = crate::BitReader;
#[doc = "Field `EN` writer - reg_t0_en."]
pub type EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 9 - reg_t0_use_xtal."]
    #[inline(always)]
    pub fn use_xtal(&self) -> USE_XTAL_R {
        USE_XTAL_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - reg_t0_alarm_en."]
    #[inline(always)]
    pub fn alarm_en(&self) -> ALARM_EN_R {
        ALARM_EN_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bits 13:28 - reg_t0_divider."]
    #[inline(always)]
    pub fn divider(&self) -> DIVIDER_R {
        DIVIDER_R::new(((self.bits >> 13) & 0xffff) as u16)
    }
    #[doc = "Bit 29 - reg_t0_autoreload."]
    #[inline(always)]
    pub fn autoreload(&self) -> AUTORELOAD_R {
        AUTORELOAD_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - reg_t0_increase."]
    #[inline(always)]
    pub fn increase(&self) -> INCREASE_R {
        INCREASE_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - reg_t0_en."]
    #[inline(always)]
    pub fn en(&self) -> EN_R {
        EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONFIG")
            .field("use_xtal", &self.use_xtal())
            .field("alarm_en", &self.alarm_en())
            .field("divider", &self.divider())
            .field("autoreload", &self.autoreload())
            .field("increase", &self.increase())
            .field("en", &self.en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 9 - reg_t0_use_xtal."]
    #[inline(always)]
    pub fn use_xtal(&mut self) -> USE_XTAL_W<'_, CONFIG_SPEC> {
        USE_XTAL_W::new(self, 9)
    }
    #[doc = "Bit 10 - reg_t0_alarm_en."]
    #[inline(always)]
    pub fn alarm_en(&mut self) -> ALARM_EN_W<'_, CONFIG_SPEC> {
        ALARM_EN_W::new(self, 10)
    }
    #[doc = "Bit 12 - reg_t0_divcnt_rst."]
    #[inline(always)]
    pub fn divcnt_rst(&mut self) -> DIVCNT_RST_W<'_, CONFIG_SPEC> {
        DIVCNT_RST_W::new(self, 12)
    }
    #[doc = "Bits 13:28 - reg_t0_divider."]
    #[inline(always)]
    pub fn divider(&mut self) -> DIVIDER_W<'_, CONFIG_SPEC> {
        DIVIDER_W::new(self, 13)
    }
    #[doc = "Bit 29 - reg_t0_autoreload."]
    #[inline(always)]
    pub fn autoreload(&mut self) -> AUTORELOAD_W<'_, CONFIG_SPEC> {
        AUTORELOAD_W::new(self, 29)
    }
    #[doc = "Bit 30 - reg_t0_increase."]
    #[inline(always)]
    pub fn increase(&mut self) -> INCREASE_W<'_, CONFIG_SPEC> {
        INCREASE_W::new(self, 30)
    }
    #[doc = "Bit 31 - reg_t0_en."]
    #[inline(always)]
    pub fn en(&mut self) -> EN_W<'_, CONFIG_SPEC> {
        EN_W::new(self, 31)
    }
}
#[doc = "TIMG_T0CONFIG_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`config::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`config::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONFIG_SPEC;
impl crate::RegisterSpec for CONFIG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`config::R`](R) reader structure"]
impl crate::Readable for CONFIG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`config::W`](W) writer structure"]
impl crate::Writable for CONFIG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONFIG to value 0x6000_2000"]
impl crate::Resettable for CONFIG_SPEC {
    const RESET_VALUE: u32 = 0x6000_2000;
}
