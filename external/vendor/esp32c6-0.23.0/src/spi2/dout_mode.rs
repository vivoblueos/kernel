#[doc = "Register `DOUT_MODE` reader"]
pub type R = crate::R<DOUT_MODE_SPEC>;
#[doc = "Register `DOUT_MODE` writer"]
pub type W = crate::W<DOUT_MODE_SPEC>;
#[doc = "Field `DOUT0_MODE` reader - The output signal 0 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type DOUT0_MODE_R = crate::BitReader;
#[doc = "Field `DOUT0_MODE` writer - The output signal 0 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type DOUT0_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DOUT1_MODE` reader - The output signal 1 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type DOUT1_MODE_R = crate::BitReader;
#[doc = "Field `DOUT1_MODE` writer - The output signal 1 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type DOUT1_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DOUT2_MODE` reader - The output signal 2 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type DOUT2_MODE_R = crate::BitReader;
#[doc = "Field `DOUT2_MODE` writer - The output signal 2 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type DOUT2_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DOUT3_MODE` reader - The output signal 3 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type DOUT3_MODE_R = crate::BitReader;
#[doc = "Field `DOUT3_MODE` writer - The output signal 3 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type DOUT3_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DOUT4_MODE` reader - The output signal 4 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type DOUT4_MODE_R = crate::BitReader;
#[doc = "Field `DOUT5_MODE` reader - The output signal 5 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type DOUT5_MODE_R = crate::BitReader;
#[doc = "Field `DOUT6_MODE` reader - The output signal 6 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type DOUT6_MODE_R = crate::BitReader;
#[doc = "Field `DOUT7_MODE` reader - The output signal 7 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type DOUT7_MODE_R = crate::BitReader;
#[doc = "Field `D_DQS_MODE` reader - The output signal SPI_DQS is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
pub type D_DQS_MODE_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The output signal 0 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn dout0_mode(&self) -> DOUT0_MODE_R {
        DOUT0_MODE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The output signal 1 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn dout1_mode(&self) -> DOUT1_MODE_R {
        DOUT1_MODE_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The output signal 2 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn dout2_mode(&self) -> DOUT2_MODE_R {
        DOUT2_MODE_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The output signal 3 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn dout3_mode(&self) -> DOUT3_MODE_R {
        DOUT3_MODE_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The output signal 4 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn dout4_mode(&self) -> DOUT4_MODE_R {
        DOUT4_MODE_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The output signal 5 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn dout5_mode(&self) -> DOUT5_MODE_R {
        DOUT5_MODE_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The output signal 6 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn dout6_mode(&self) -> DOUT6_MODE_R {
        DOUT6_MODE_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The output signal 7 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn dout7_mode(&self) -> DOUT7_MODE_R {
        DOUT7_MODE_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The output signal SPI_DQS is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn d_dqs_mode(&self) -> D_DQS_MODE_R {
        D_DQS_MODE_R::new(((self.bits >> 8) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DOUT_MODE")
            .field("dout0_mode", &self.dout0_mode())
            .field("dout1_mode", &self.dout1_mode())
            .field("dout2_mode", &self.dout2_mode())
            .field("dout3_mode", &self.dout3_mode())
            .field("dout4_mode", &self.dout4_mode())
            .field("dout5_mode", &self.dout5_mode())
            .field("dout6_mode", &self.dout6_mode())
            .field("dout7_mode", &self.dout7_mode())
            .field("d_dqs_mode", &self.d_dqs_mode())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The output signal 0 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn dout0_mode(&mut self) -> DOUT0_MODE_W<'_, DOUT_MODE_SPEC> {
        DOUT0_MODE_W::new(self, 0)
    }
    #[doc = "Bit 1 - The output signal 1 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn dout1_mode(&mut self) -> DOUT1_MODE_W<'_, DOUT_MODE_SPEC> {
        DOUT1_MODE_W::new(self, 1)
    }
    #[doc = "Bit 2 - The output signal 2 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn dout2_mode(&mut self) -> DOUT2_MODE_W<'_, DOUT_MODE_SPEC> {
        DOUT2_MODE_W::new(self, 2)
    }
    #[doc = "Bit 3 - The output signal 3 is delayed by the SPI module clock, 0: output without delayed, 1: output delay for a SPI module clock cycle at its negative edge. Can be configured in CONF state."]
    #[inline(always)]
    pub fn dout3_mode(&mut self) -> DOUT3_MODE_W<'_, DOUT_MODE_SPEC> {
        DOUT3_MODE_W::new(self, 3)
    }
}
#[doc = "SPI output delay mode configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`dout_mode::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dout_mode::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DOUT_MODE_SPEC;
impl crate::RegisterSpec for DOUT_MODE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dout_mode::R`](R) reader structure"]
impl crate::Readable for DOUT_MODE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dout_mode::W`](W) writer structure"]
impl crate::Writable for DOUT_MODE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DOUT_MODE to value 0"]
impl crate::Resettable for DOUT_MODE_SPEC {}
