#[doc = "Register `TX_TIMING` reader"]
pub type R = crate::R<TX_TIMING_SPEC>;
#[doc = "Register `TX_TIMING` writer"]
pub type W = crate::W<TX_TIMING_SPEC>;
#[doc = "Field `TX_SD_OUT_DM` reader - The delay mode of I2S TX SD output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
pub type TX_SD_OUT_DM_R = crate::FieldReader;
#[doc = "Field `TX_SD_OUT_DM` writer - The delay mode of I2S TX SD output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
pub type TX_SD_OUT_DM_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `TX_SD1_OUT_DM` reader - The delay mode of I2S TX SD1 output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
pub type TX_SD1_OUT_DM_R = crate::FieldReader;
#[doc = "Field `TX_SD1_OUT_DM` writer - The delay mode of I2S TX SD1 output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
pub type TX_SD1_OUT_DM_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `TX_WS_OUT_DM` reader - The delay mode of I2S TX WS output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
pub type TX_WS_OUT_DM_R = crate::FieldReader;
#[doc = "Field `TX_WS_OUT_DM` writer - The delay mode of I2S TX WS output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
pub type TX_WS_OUT_DM_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `TX_BCK_OUT_DM` reader - The delay mode of I2S TX BCK output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
pub type TX_BCK_OUT_DM_R = crate::FieldReader;
#[doc = "Field `TX_BCK_OUT_DM` writer - The delay mode of I2S TX BCK output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
pub type TX_BCK_OUT_DM_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `TX_WS_IN_DM` reader - The delay mode of I2S TX WS input signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
pub type TX_WS_IN_DM_R = crate::FieldReader;
#[doc = "Field `TX_WS_IN_DM` writer - The delay mode of I2S TX WS input signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
pub type TX_WS_IN_DM_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `TX_BCK_IN_DM` reader - The delay mode of I2S TX BCK input signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
pub type TX_BCK_IN_DM_R = crate::FieldReader;
#[doc = "Field `TX_BCK_IN_DM` writer - The delay mode of I2S TX BCK input signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
pub type TX_BCK_IN_DM_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:1 - The delay mode of I2S TX SD output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
    #[inline(always)]
    pub fn tx_sd_out_dm(&self) -> TX_SD_OUT_DM_R {
        TX_SD_OUT_DM_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 4:5 - The delay mode of I2S TX SD1 output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
    #[inline(always)]
    pub fn tx_sd1_out_dm(&self) -> TX_SD1_OUT_DM_R {
        TX_SD1_OUT_DM_R::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bits 16:17 - The delay mode of I2S TX WS output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
    #[inline(always)]
    pub fn tx_ws_out_dm(&self) -> TX_WS_OUT_DM_R {
        TX_WS_OUT_DM_R::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 20:21 - The delay mode of I2S TX BCK output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
    #[inline(always)]
    pub fn tx_bck_out_dm(&self) -> TX_BCK_OUT_DM_R {
        TX_BCK_OUT_DM_R::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bits 24:25 - The delay mode of I2S TX WS input signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
    #[inline(always)]
    pub fn tx_ws_in_dm(&self) -> TX_WS_IN_DM_R {
        TX_WS_IN_DM_R::new(((self.bits >> 24) & 3) as u8)
    }
    #[doc = "Bits 28:29 - The delay mode of I2S TX BCK input signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
    #[inline(always)]
    pub fn tx_bck_in_dm(&self) -> TX_BCK_IN_DM_R {
        TX_BCK_IN_DM_R::new(((self.bits >> 28) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_TIMING")
            .field("tx_sd_out_dm", &self.tx_sd_out_dm())
            .field("tx_sd1_out_dm", &self.tx_sd1_out_dm())
            .field("tx_ws_out_dm", &self.tx_ws_out_dm())
            .field("tx_bck_out_dm", &self.tx_bck_out_dm())
            .field("tx_ws_in_dm", &self.tx_ws_in_dm())
            .field("tx_bck_in_dm", &self.tx_bck_in_dm())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - The delay mode of I2S TX SD output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
    #[inline(always)]
    pub fn tx_sd_out_dm(&mut self) -> TX_SD_OUT_DM_W<'_, TX_TIMING_SPEC> {
        TX_SD_OUT_DM_W::new(self, 0)
    }
    #[doc = "Bits 4:5 - The delay mode of I2S TX SD1 output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
    #[inline(always)]
    pub fn tx_sd1_out_dm(&mut self) -> TX_SD1_OUT_DM_W<'_, TX_TIMING_SPEC> {
        TX_SD1_OUT_DM_W::new(self, 4)
    }
    #[doc = "Bits 16:17 - The delay mode of I2S TX WS output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
    #[inline(always)]
    pub fn tx_ws_out_dm(&mut self) -> TX_WS_OUT_DM_W<'_, TX_TIMING_SPEC> {
        TX_WS_OUT_DM_W::new(self, 16)
    }
    #[doc = "Bits 20:21 - The delay mode of I2S TX BCK output signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
    #[inline(always)]
    pub fn tx_bck_out_dm(&mut self) -> TX_BCK_OUT_DM_W<'_, TX_TIMING_SPEC> {
        TX_BCK_OUT_DM_W::new(self, 20)
    }
    #[doc = "Bits 24:25 - The delay mode of I2S TX WS input signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
    #[inline(always)]
    pub fn tx_ws_in_dm(&mut self) -> TX_WS_IN_DM_W<'_, TX_TIMING_SPEC> {
        TX_WS_IN_DM_W::new(self, 24)
    }
    #[doc = "Bits 28:29 - The delay mode of I2S TX BCK input signal. 0: bypass. 1: delay by pos edge. 2: delay by neg edge. 3: not used."]
    #[inline(always)]
    pub fn tx_bck_in_dm(&mut self) -> TX_BCK_IN_DM_W<'_, TX_TIMING_SPEC> {
        TX_BCK_IN_DM_W::new(self, 28)
    }
}
#[doc = "I2S TX timing control register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_timing::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_timing::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_TIMING_SPEC;
impl crate::RegisterSpec for TX_TIMING_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_timing::R`](R) reader structure"]
impl crate::Readable for TX_TIMING_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_timing::W`](W) writer structure"]
impl crate::Writable for TX_TIMING_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_TIMING to value 0"]
impl crate::Resettable for TX_TIMING_SPEC {}
