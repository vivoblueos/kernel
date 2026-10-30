#[doc = "Register `WR_TIM_CONF0_RS_BYPASS` reader"]
pub type R = crate::R<WR_TIM_CONF0_RS_BYPASS_SPEC>;
#[doc = "Register `WR_TIM_CONF0_RS_BYPASS` writer"]
pub type W = crate::W<WR_TIM_CONF0_RS_BYPASS_SPEC>;
#[doc = "Field `BYPASS_RS_CORRECTION` reader - Set this bit to bypass reed solomon correction step."]
pub type BYPASS_RS_CORRECTION_R = crate::BitReader;
#[doc = "Field `BYPASS_RS_CORRECTION` writer - Set this bit to bypass reed solomon correction step."]
pub type BYPASS_RS_CORRECTION_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BYPASS_RS_BLK_NUM` reader - Configures block number of programming twice operation."]
pub type BYPASS_RS_BLK_NUM_R = crate::FieldReader<u16>;
#[doc = "Field `BYPASS_RS_BLK_NUM` writer - Configures block number of programming twice operation."]
pub type BYPASS_RS_BLK_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 11, u16>;
#[doc = "Field `UPDATE` writer - Set this bit to update multi-bit register signals."]
pub type UPDATE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TPGM_INACTIVE` reader - Configures the inactive programming time."]
pub type TPGM_INACTIVE_R = crate::FieldReader;
#[doc = "Field `TPGM_INACTIVE` writer - Configures the inactive programming time."]
pub type TPGM_INACTIVE_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bit 0 - Set this bit to bypass reed solomon correction step."]
    #[inline(always)]
    pub fn bypass_rs_correction(&self) -> BYPASS_RS_CORRECTION_R {
        BYPASS_RS_CORRECTION_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:11 - Configures block number of programming twice operation."]
    #[inline(always)]
    pub fn bypass_rs_blk_num(&self) -> BYPASS_RS_BLK_NUM_R {
        BYPASS_RS_BLK_NUM_R::new(((self.bits >> 1) & 0x07ff) as u16)
    }
    #[doc = "Bits 13:20 - Configures the inactive programming time."]
    #[inline(always)]
    pub fn tpgm_inactive(&self) -> TPGM_INACTIVE_R {
        TPGM_INACTIVE_R::new(((self.bits >> 13) & 0xff) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("WR_TIM_CONF0_RS_BYPASS")
            .field("bypass_rs_correction", &self.bypass_rs_correction())
            .field("bypass_rs_blk_num", &self.bypass_rs_blk_num())
            .field("tpgm_inactive", &self.tpgm_inactive())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit to bypass reed solomon correction step."]
    #[inline(always)]
    pub fn bypass_rs_correction(
        &mut self,
    ) -> BYPASS_RS_CORRECTION_W<'_, WR_TIM_CONF0_RS_BYPASS_SPEC> {
        BYPASS_RS_CORRECTION_W::new(self, 0)
    }
    #[doc = "Bits 1:11 - Configures block number of programming twice operation."]
    #[inline(always)]
    pub fn bypass_rs_blk_num(&mut self) -> BYPASS_RS_BLK_NUM_W<'_, WR_TIM_CONF0_RS_BYPASS_SPEC> {
        BYPASS_RS_BLK_NUM_W::new(self, 1)
    }
    #[doc = "Bit 12 - Set this bit to update multi-bit register signals."]
    #[inline(always)]
    pub fn update(&mut self) -> UPDATE_W<'_, WR_TIM_CONF0_RS_BYPASS_SPEC> {
        UPDATE_W::new(self, 12)
    }
    #[doc = "Bits 13:20 - Configures the inactive programming time."]
    #[inline(always)]
    pub fn tpgm_inactive(&mut self) -> TPGM_INACTIVE_W<'_, WR_TIM_CONF0_RS_BYPASS_SPEC> {
        TPGM_INACTIVE_W::new(self, 13)
    }
}
#[doc = "Configurarion register0 of eFuse programming time parameters and rs bypass operation.\n\nYou can [`read`](crate::Reg::read) this register and get [`wr_tim_conf0_rs_bypass::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wr_tim_conf0_rs_bypass::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct WR_TIM_CONF0_RS_BYPASS_SPEC;
impl crate::RegisterSpec for WR_TIM_CONF0_RS_BYPASS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`wr_tim_conf0_rs_bypass::R`](R) reader structure"]
impl crate::Readable for WR_TIM_CONF0_RS_BYPASS_SPEC {}
#[doc = "`write(|w| ..)` method takes [`wr_tim_conf0_rs_bypass::W`](W) writer structure"]
impl crate::Writable for WR_TIM_CONF0_RS_BYPASS_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets WR_TIM_CONF0_RS_BYPASS to value 0x2000"]
impl crate::Resettable for WR_TIM_CONF0_RS_BYPASS_SPEC {
    const RESET_VALUE: u32 = 0x2000;
}
