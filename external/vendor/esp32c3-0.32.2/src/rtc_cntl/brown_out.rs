#[doc = "Register `BROWN_OUT` reader"]
pub type R = crate::R<BROWN_OUT_SPEC>;
#[doc = "Register `BROWN_OUT` writer"]
pub type W = crate::W<BROWN_OUT_SPEC>;
#[doc = "Field `BROWN_OUT_INT_WAIT` reader - brown out interrupt wait cycles"]
pub type BROWN_OUT_INT_WAIT_R = crate::FieldReader<u16>;
#[doc = "Field `BROWN_OUT_INT_WAIT` writer - brown out interrupt wait cycles"]
pub type BROWN_OUT_INT_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `BROWN_OUT_CLOSE_FLASH_ENA` reader - enable close flash when brown out happens"]
pub type BROWN_OUT_CLOSE_FLASH_ENA_R = crate::BitReader;
#[doc = "Field `BROWN_OUT_CLOSE_FLASH_ENA` writer - enable close flash when brown out happens"]
pub type BROWN_OUT_CLOSE_FLASH_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BROWN_OUT_PD_RF_ENA` reader - enable power down RF when brown out happens"]
pub type BROWN_OUT_PD_RF_ENA_R = crate::BitReader;
#[doc = "Field `BROWN_OUT_PD_RF_ENA` writer - enable power down RF when brown out happens"]
pub type BROWN_OUT_PD_RF_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BROWN_OUT_RST_WAIT` reader - brown out reset wait cycles"]
pub type BROWN_OUT_RST_WAIT_R = crate::FieldReader<u16>;
#[doc = "Field `BROWN_OUT_RST_WAIT` writer - brown out reset wait cycles"]
pub type BROWN_OUT_RST_WAIT_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `BROWN_OUT_RST_ENA` reader - enable brown out reset"]
pub type BROWN_OUT_RST_ENA_R = crate::BitReader;
#[doc = "Field `BROWN_OUT_RST_ENA` writer - enable brown out reset"]
pub type BROWN_OUT_RST_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BROWN_OUT_RST_SEL` reader - 1: 4-pos reset"]
pub type BROWN_OUT_RST_SEL_R = crate::BitReader;
#[doc = "Field `BROWN_OUT_RST_SEL` writer - 1: 4-pos reset"]
pub type BROWN_OUT_RST_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BROWN_OUT_ANA_RST_EN` reader - brown_out origin reset enable"]
pub type BROWN_OUT_ANA_RST_EN_R = crate::BitReader;
#[doc = "Field `BROWN_OUT_ANA_RST_EN` writer - brown_out origin reset enable"]
pub type BROWN_OUT_ANA_RST_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BROWN_OUT_CNT_CLR` writer - clear brown out counter"]
pub type BROWN_OUT_CNT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BROWN_OUT_ENA` reader - enable brown out"]
pub type BROWN_OUT_ENA_R = crate::BitReader;
#[doc = "Field `BROWN_OUT_ENA` writer - enable brown out"]
pub type BROWN_OUT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DET` reader - the flag of brown det from analog"]
pub type DET_R = crate::BitReader;
impl R {
    #[doc = "Bits 4:13 - brown out interrupt wait cycles"]
    #[inline(always)]
    pub fn brown_out_int_wait(&self) -> BROWN_OUT_INT_WAIT_R {
        BROWN_OUT_INT_WAIT_R::new(((self.bits >> 4) & 0x03ff) as u16)
    }
    #[doc = "Bit 14 - enable close flash when brown out happens"]
    #[inline(always)]
    pub fn brown_out_close_flash_ena(&self) -> BROWN_OUT_CLOSE_FLASH_ENA_R {
        BROWN_OUT_CLOSE_FLASH_ENA_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - enable power down RF when brown out happens"]
    #[inline(always)]
    pub fn brown_out_pd_rf_ena(&self) -> BROWN_OUT_PD_RF_ENA_R {
        BROWN_OUT_PD_RF_ENA_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 16:25 - brown out reset wait cycles"]
    #[inline(always)]
    pub fn brown_out_rst_wait(&self) -> BROWN_OUT_RST_WAIT_R {
        BROWN_OUT_RST_WAIT_R::new(((self.bits >> 16) & 0x03ff) as u16)
    }
    #[doc = "Bit 26 - enable brown out reset"]
    #[inline(always)]
    pub fn brown_out_rst_ena(&self) -> BROWN_OUT_RST_ENA_R {
        BROWN_OUT_RST_ENA_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - 1: 4-pos reset"]
    #[inline(always)]
    pub fn brown_out_rst_sel(&self) -> BROWN_OUT_RST_SEL_R {
        BROWN_OUT_RST_SEL_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - brown_out origin reset enable"]
    #[inline(always)]
    pub fn brown_out_ana_rst_en(&self) -> BROWN_OUT_ANA_RST_EN_R {
        BROWN_OUT_ANA_RST_EN_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 30 - enable brown out"]
    #[inline(always)]
    pub fn brown_out_ena(&self) -> BROWN_OUT_ENA_R {
        BROWN_OUT_ENA_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - the flag of brown det from analog"]
    #[inline(always)]
    pub fn det(&self) -> DET_R {
        DET_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BROWN_OUT")
            .field("brown_out_int_wait", &self.brown_out_int_wait())
            .field(
                "brown_out_close_flash_ena",
                &self.brown_out_close_flash_ena(),
            )
            .field("brown_out_pd_rf_ena", &self.brown_out_pd_rf_ena())
            .field("brown_out_rst_wait", &self.brown_out_rst_wait())
            .field("brown_out_rst_ena", &self.brown_out_rst_ena())
            .field("brown_out_rst_sel", &self.brown_out_rst_sel())
            .field("brown_out_ana_rst_en", &self.brown_out_ana_rst_en())
            .field("brown_out_ena", &self.brown_out_ena())
            .field("det", &self.det())
            .finish()
    }
}
impl W {
    #[doc = "Bits 4:13 - brown out interrupt wait cycles"]
    #[inline(always)]
    pub fn brown_out_int_wait(&mut self) -> BROWN_OUT_INT_WAIT_W<'_, BROWN_OUT_SPEC> {
        BROWN_OUT_INT_WAIT_W::new(self, 4)
    }
    #[doc = "Bit 14 - enable close flash when brown out happens"]
    #[inline(always)]
    pub fn brown_out_close_flash_ena(&mut self) -> BROWN_OUT_CLOSE_FLASH_ENA_W<'_, BROWN_OUT_SPEC> {
        BROWN_OUT_CLOSE_FLASH_ENA_W::new(self, 14)
    }
    #[doc = "Bit 15 - enable power down RF when brown out happens"]
    #[inline(always)]
    pub fn brown_out_pd_rf_ena(&mut self) -> BROWN_OUT_PD_RF_ENA_W<'_, BROWN_OUT_SPEC> {
        BROWN_OUT_PD_RF_ENA_W::new(self, 15)
    }
    #[doc = "Bits 16:25 - brown out reset wait cycles"]
    #[inline(always)]
    pub fn brown_out_rst_wait(&mut self) -> BROWN_OUT_RST_WAIT_W<'_, BROWN_OUT_SPEC> {
        BROWN_OUT_RST_WAIT_W::new(self, 16)
    }
    #[doc = "Bit 26 - enable brown out reset"]
    #[inline(always)]
    pub fn brown_out_rst_ena(&mut self) -> BROWN_OUT_RST_ENA_W<'_, BROWN_OUT_SPEC> {
        BROWN_OUT_RST_ENA_W::new(self, 26)
    }
    #[doc = "Bit 27 - 1: 4-pos reset"]
    #[inline(always)]
    pub fn brown_out_rst_sel(&mut self) -> BROWN_OUT_RST_SEL_W<'_, BROWN_OUT_SPEC> {
        BROWN_OUT_RST_SEL_W::new(self, 27)
    }
    #[doc = "Bit 28 - brown_out origin reset enable"]
    #[inline(always)]
    pub fn brown_out_ana_rst_en(&mut self) -> BROWN_OUT_ANA_RST_EN_W<'_, BROWN_OUT_SPEC> {
        BROWN_OUT_ANA_RST_EN_W::new(self, 28)
    }
    #[doc = "Bit 29 - clear brown out counter"]
    #[inline(always)]
    pub fn brown_out_cnt_clr(&mut self) -> BROWN_OUT_CNT_CLR_W<'_, BROWN_OUT_SPEC> {
        BROWN_OUT_CNT_CLR_W::new(self, 29)
    }
    #[doc = "Bit 30 - enable brown out"]
    #[inline(always)]
    pub fn brown_out_ena(&mut self) -> BROWN_OUT_ENA_W<'_, BROWN_OUT_SPEC> {
        BROWN_OUT_ENA_W::new(self, 30)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`brown_out::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`brown_out::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BROWN_OUT_SPEC;
impl crate::RegisterSpec for BROWN_OUT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`brown_out::R`](R) reader structure"]
impl crate::Readable for BROWN_OUT_SPEC {}
#[doc = "`write(|w| ..)` method takes [`brown_out::W`](W) writer structure"]
impl crate::Writable for BROWN_OUT_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets BROWN_OUT to value 0x43ff_0010"]
impl crate::Resettable for BROWN_OUT_SPEC {
    const RESET_VALUE: u32 = 0x43ff_0010;
}
