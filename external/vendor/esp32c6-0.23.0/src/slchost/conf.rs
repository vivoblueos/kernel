#[doc = "Register `CONF` reader"]
pub type R = crate::R<CONF_SPEC>;
#[doc = "Register `CONF` writer"]
pub type W = crate::W<CONF_SPEC>;
#[doc = "Field `FRC_SDIO11` reader - *******Description***********"]
pub type FRC_SDIO11_R = crate::FieldReader;
#[doc = "Field `FRC_SDIO11` writer - *******Description***********"]
pub type FRC_SDIO11_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `FRC_SDIO20` reader - *******Description***********"]
pub type FRC_SDIO20_R = crate::FieldReader;
#[doc = "Field `FRC_SDIO20` writer - *******Description***********"]
pub type FRC_SDIO20_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `FRC_NEG_SAMP` reader - *******Description***********"]
pub type FRC_NEG_SAMP_R = crate::FieldReader;
#[doc = "Field `FRC_NEG_SAMP` writer - *******Description***********"]
pub type FRC_NEG_SAMP_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `FRC_POS_SAMP` reader - *******Description***********"]
pub type FRC_POS_SAMP_R = crate::FieldReader;
#[doc = "Field `FRC_POS_SAMP` writer - *******Description***********"]
pub type FRC_POS_SAMP_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `FRC_QUICK_IN` reader - *******Description***********"]
pub type FRC_QUICK_IN_R = crate::FieldReader;
#[doc = "Field `FRC_QUICK_IN` writer - *******Description***********"]
pub type FRC_QUICK_IN_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `SDIO20_INT_DELAY` reader - *******Description***********"]
pub type SDIO20_INT_DELAY_R = crate::BitReader;
#[doc = "Field `SDIO20_INT_DELAY` writer - *******Description***********"]
pub type SDIO20_INT_DELAY_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_PAD_PULLUP` reader - *******Description***********"]
pub type SDIO_PAD_PULLUP_R = crate::BitReader;
#[doc = "Field `SDIO_PAD_PULLUP` writer - *******Description***********"]
pub type SDIO_PAD_PULLUP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HSPEED_CON_EN` reader - *******Description***********"]
pub type HSPEED_CON_EN_R = crate::BitReader;
#[doc = "Field `HSPEED_CON_EN` writer - *******Description***********"]
pub type HSPEED_CON_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:4 - *******Description***********"]
    #[inline(always)]
    pub fn frc_sdio11(&self) -> FRC_SDIO11_R {
        FRC_SDIO11_R::new((self.bits & 0x1f) as u8)
    }
    #[doc = "Bits 5:9 - *******Description***********"]
    #[inline(always)]
    pub fn frc_sdio20(&self) -> FRC_SDIO20_R {
        FRC_SDIO20_R::new(((self.bits >> 5) & 0x1f) as u8)
    }
    #[doc = "Bits 10:14 - *******Description***********"]
    #[inline(always)]
    pub fn frc_neg_samp(&self) -> FRC_NEG_SAMP_R {
        FRC_NEG_SAMP_R::new(((self.bits >> 10) & 0x1f) as u8)
    }
    #[doc = "Bits 15:19 - *******Description***********"]
    #[inline(always)]
    pub fn frc_pos_samp(&self) -> FRC_POS_SAMP_R {
        FRC_POS_SAMP_R::new(((self.bits >> 15) & 0x1f) as u8)
    }
    #[doc = "Bits 20:24 - *******Description***********"]
    #[inline(always)]
    pub fn frc_quick_in(&self) -> FRC_QUICK_IN_R {
        FRC_QUICK_IN_R::new(((self.bits >> 20) & 0x1f) as u8)
    }
    #[doc = "Bit 25 - *******Description***********"]
    #[inline(always)]
    pub fn sdio20_int_delay(&self) -> SDIO20_INT_DELAY_R {
        SDIO20_INT_DELAY_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - *******Description***********"]
    #[inline(always)]
    pub fn sdio_pad_pullup(&self) -> SDIO_PAD_PULLUP_R {
        SDIO_PAD_PULLUP_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - *******Description***********"]
    #[inline(always)]
    pub fn hspeed_con_en(&self) -> HSPEED_CON_EN_R {
        HSPEED_CON_EN_R::new(((self.bits >> 27) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF")
            .field("frc_sdio11", &self.frc_sdio11())
            .field("frc_sdio20", &self.frc_sdio20())
            .field("frc_neg_samp", &self.frc_neg_samp())
            .field("frc_pos_samp", &self.frc_pos_samp())
            .field("frc_quick_in", &self.frc_quick_in())
            .field("sdio20_int_delay", &self.sdio20_int_delay())
            .field("sdio_pad_pullup", &self.sdio_pad_pullup())
            .field("hspeed_con_en", &self.hspeed_con_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:4 - *******Description***********"]
    #[inline(always)]
    pub fn frc_sdio11(&mut self) -> FRC_SDIO11_W<'_, CONF_SPEC> {
        FRC_SDIO11_W::new(self, 0)
    }
    #[doc = "Bits 5:9 - *******Description***********"]
    #[inline(always)]
    pub fn frc_sdio20(&mut self) -> FRC_SDIO20_W<'_, CONF_SPEC> {
        FRC_SDIO20_W::new(self, 5)
    }
    #[doc = "Bits 10:14 - *******Description***********"]
    #[inline(always)]
    pub fn frc_neg_samp(&mut self) -> FRC_NEG_SAMP_W<'_, CONF_SPEC> {
        FRC_NEG_SAMP_W::new(self, 10)
    }
    #[doc = "Bits 15:19 - *******Description***********"]
    #[inline(always)]
    pub fn frc_pos_samp(&mut self) -> FRC_POS_SAMP_W<'_, CONF_SPEC> {
        FRC_POS_SAMP_W::new(self, 15)
    }
    #[doc = "Bits 20:24 - *******Description***********"]
    #[inline(always)]
    pub fn frc_quick_in(&mut self) -> FRC_QUICK_IN_W<'_, CONF_SPEC> {
        FRC_QUICK_IN_W::new(self, 20)
    }
    #[doc = "Bit 25 - *******Description***********"]
    #[inline(always)]
    pub fn sdio20_int_delay(&mut self) -> SDIO20_INT_DELAY_W<'_, CONF_SPEC> {
        SDIO20_INT_DELAY_W::new(self, 25)
    }
    #[doc = "Bit 26 - *******Description***********"]
    #[inline(always)]
    pub fn sdio_pad_pullup(&mut self) -> SDIO_PAD_PULLUP_W<'_, CONF_SPEC> {
        SDIO_PAD_PULLUP_W::new(self, 26)
    }
    #[doc = "Bit 27 - *******Description***********"]
    #[inline(always)]
    pub fn hspeed_con_en(&mut self) -> HSPEED_CON_EN_W<'_, CONF_SPEC> {
        HSPEED_CON_EN_W::new(self, 27)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF_SPEC;
impl crate::RegisterSpec for CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf::R`](R) reader structure"]
impl crate::Readable for CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf::W`](W) writer structure"]
impl crate::Writable for CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF to value 0"]
impl crate::Resettable for CONF_SPEC {}
