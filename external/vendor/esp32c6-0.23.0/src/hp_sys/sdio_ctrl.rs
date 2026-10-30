#[doc = "Register `SDIO_CTRL` reader"]
pub type R = crate::R<SDIO_CTRL_SPEC>;
#[doc = "Register `SDIO_CTRL` writer"]
pub type W = crate::W<SDIO_CTRL_SPEC>;
#[doc = "Field `DIS_SDIO_PROB` reader - Set this bit as 1 to disable SDIO_PROB function. disable by default."]
pub type DIS_SDIO_PROB_R = crate::BitReader;
#[doc = "Field `DIS_SDIO_PROB` writer - Set this bit as 1 to disable SDIO_PROB function. disable by default."]
pub type DIS_SDIO_PROB_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_WIN_ACCESS_EN` reader - Enable sdio slave to access other peripherals on the chip"]
pub type SDIO_WIN_ACCESS_EN_R = crate::BitReader;
#[doc = "Field `SDIO_WIN_ACCESS_EN` writer - Enable sdio slave to access other peripherals on the chip"]
pub type SDIO_WIN_ACCESS_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set this bit as 1 to disable SDIO_PROB function. disable by default."]
    #[inline(always)]
    pub fn dis_sdio_prob(&self) -> DIS_SDIO_PROB_R {
        DIS_SDIO_PROB_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Enable sdio slave to access other peripherals on the chip"]
    #[inline(always)]
    pub fn sdio_win_access_en(&self) -> SDIO_WIN_ACCESS_EN_R {
        SDIO_WIN_ACCESS_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SDIO_CTRL")
            .field("dis_sdio_prob", &self.dis_sdio_prob())
            .field("sdio_win_access_en", &self.sdio_win_access_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit as 1 to disable SDIO_PROB function. disable by default."]
    #[inline(always)]
    pub fn dis_sdio_prob(&mut self) -> DIS_SDIO_PROB_W<'_, SDIO_CTRL_SPEC> {
        DIS_SDIO_PROB_W::new(self, 0)
    }
    #[doc = "Bit 1 - Enable sdio slave to access other peripherals on the chip"]
    #[inline(always)]
    pub fn sdio_win_access_en(&mut self) -> SDIO_WIN_ACCESS_EN_W<'_, SDIO_CTRL_SPEC> {
        SDIO_WIN_ACCESS_EN_W::new(self, 1)
    }
}
#[doc = "SDIO Control configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sdio_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sdio_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SDIO_CTRL_SPEC;
impl crate::RegisterSpec for SDIO_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sdio_ctrl::R`](R) reader structure"]
impl crate::Readable for SDIO_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sdio_ctrl::W`](W) writer structure"]
impl crate::Writable for SDIO_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SDIO_CTRL to value 0x03"]
impl crate::Resettable for SDIO_CTRL_SPEC {
    const RESET_VALUE: u32 = 0x03;
}
