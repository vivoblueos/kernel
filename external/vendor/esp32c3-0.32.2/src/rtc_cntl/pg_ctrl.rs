#[doc = "Register `PG_CTRL` reader"]
pub type R = crate::R<PG_CTRL_SPEC>;
#[doc = "Register `PG_CTRL` writer"]
pub type W = crate::W<PG_CTRL_SPEC>;
#[doc = "Field `POWER_GLITCH_DSENSE` reader - power glitch desense"]
pub type POWER_GLITCH_DSENSE_R = crate::FieldReader;
#[doc = "Field `POWER_GLITCH_DSENSE` writer - power glitch desense"]
pub type POWER_GLITCH_DSENSE_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `POWER_GLITCH_FORCE_PD` reader - force disable power glitch"]
pub type POWER_GLITCH_FORCE_PD_R = crate::BitReader;
#[doc = "Field `POWER_GLITCH_FORCE_PD` writer - force disable power glitch"]
pub type POWER_GLITCH_FORCE_PD_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `POWER_GLITCH_FORCE_PU` reader - force enable power glitch"]
pub type POWER_GLITCH_FORCE_PU_R = crate::BitReader;
#[doc = "Field `POWER_GLITCH_FORCE_PU` writer - force enable power glitch"]
pub type POWER_GLITCH_FORCE_PU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `POWER_GLITCH_EFUSE_SEL` reader - use efuse value control power glitch enable"]
pub type POWER_GLITCH_EFUSE_SEL_R = crate::BitReader;
#[doc = "Field `POWER_GLITCH_EFUSE_SEL` writer - use efuse value control power glitch enable"]
pub type POWER_GLITCH_EFUSE_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `POWER_GLITCH_EN` reader - enable power glitch"]
pub type POWER_GLITCH_EN_R = crate::BitReader;
#[doc = "Field `POWER_GLITCH_EN` writer - enable power glitch"]
pub type POWER_GLITCH_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 26:27 - power glitch desense"]
    #[inline(always)]
    pub fn power_glitch_dsense(&self) -> POWER_GLITCH_DSENSE_R {
        POWER_GLITCH_DSENSE_R::new(((self.bits >> 26) & 3) as u8)
    }
    #[doc = "Bit 28 - force disable power glitch"]
    #[inline(always)]
    pub fn power_glitch_force_pd(&self) -> POWER_GLITCH_FORCE_PD_R {
        POWER_GLITCH_FORCE_PD_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - force enable power glitch"]
    #[inline(always)]
    pub fn power_glitch_force_pu(&self) -> POWER_GLITCH_FORCE_PU_R {
        POWER_GLITCH_FORCE_PU_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - use efuse value control power glitch enable"]
    #[inline(always)]
    pub fn power_glitch_efuse_sel(&self) -> POWER_GLITCH_EFUSE_SEL_R {
        POWER_GLITCH_EFUSE_SEL_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - enable power glitch"]
    #[inline(always)]
    pub fn power_glitch_en(&self) -> POWER_GLITCH_EN_R {
        POWER_GLITCH_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("PG_CTRL")
            .field("power_glitch_dsense", &self.power_glitch_dsense())
            .field("power_glitch_force_pd", &self.power_glitch_force_pd())
            .field("power_glitch_force_pu", &self.power_glitch_force_pu())
            .field("power_glitch_efuse_sel", &self.power_glitch_efuse_sel())
            .field("power_glitch_en", &self.power_glitch_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 26:27 - power glitch desense"]
    #[inline(always)]
    pub fn power_glitch_dsense(&mut self) -> POWER_GLITCH_DSENSE_W<'_, PG_CTRL_SPEC> {
        POWER_GLITCH_DSENSE_W::new(self, 26)
    }
    #[doc = "Bit 28 - force disable power glitch"]
    #[inline(always)]
    pub fn power_glitch_force_pd(&mut self) -> POWER_GLITCH_FORCE_PD_W<'_, PG_CTRL_SPEC> {
        POWER_GLITCH_FORCE_PD_W::new(self, 28)
    }
    #[doc = "Bit 29 - force enable power glitch"]
    #[inline(always)]
    pub fn power_glitch_force_pu(&mut self) -> POWER_GLITCH_FORCE_PU_W<'_, PG_CTRL_SPEC> {
        POWER_GLITCH_FORCE_PU_W::new(self, 29)
    }
    #[doc = "Bit 30 - use efuse value control power glitch enable"]
    #[inline(always)]
    pub fn power_glitch_efuse_sel(&mut self) -> POWER_GLITCH_EFUSE_SEL_W<'_, PG_CTRL_SPEC> {
        POWER_GLITCH_EFUSE_SEL_W::new(self, 30)
    }
    #[doc = "Bit 31 - enable power glitch"]
    #[inline(always)]
    pub fn power_glitch_en(&mut self) -> POWER_GLITCH_EN_W<'_, PG_CTRL_SPEC> {
        POWER_GLITCH_EN_W::new(self, 31)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`pg_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pg_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PG_CTRL_SPEC;
impl crate::RegisterSpec for PG_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pg_ctrl::R`](R) reader structure"]
impl crate::Readable for PG_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`pg_ctrl::W`](W) writer structure"]
impl crate::Writable for PG_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets PG_CTRL to value 0"]
impl crate::Resettable for PG_CTRL_SPEC {}
