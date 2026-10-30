#[doc = "Register `RESET_STATE` reader"]
pub type R = crate::R<RESET_STATE_SPEC>;
#[doc = "Register `RESET_STATE` writer"]
pub type W = crate::W<RESET_STATE_SPEC>;
#[doc = "Field `RESET_CAUSE_PROCPU` reader - reset cause of PRO CPU"]
pub type RESET_CAUSE_PROCPU_R = crate::FieldReader;
#[doc = "Field `RESET_CAUSE_APPCPU` reader - reset cause of APP CPU"]
pub type RESET_CAUSE_APPCPU_R = crate::FieldReader;
#[doc = "Field `STAT_VECTOR_SEL_APPCPU` reader - APP CPU state vector sel"]
pub type STAT_VECTOR_SEL_APPCPU_R = crate::BitReader;
#[doc = "Field `STAT_VECTOR_SEL_APPCPU` writer - APP CPU state vector sel"]
pub type STAT_VECTOR_SEL_APPCPU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STAT_VECTOR_SEL_PROCPU` reader - PRO CPU state vector sel"]
pub type STAT_VECTOR_SEL_PROCPU_R = crate::BitReader;
#[doc = "Field `STAT_VECTOR_SEL_PROCPU` writer - PRO CPU state vector sel"]
pub type STAT_VECTOR_SEL_PROCPU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ALL_RESET_FLAG_PROCPU` reader - PRO CPU reset_flag"]
pub type ALL_RESET_FLAG_PROCPU_R = crate::BitReader;
#[doc = "Field `ALL_RESET_FLAG_APPCPU` reader - APP CPU reset flag"]
pub type ALL_RESET_FLAG_APPCPU_R = crate::BitReader;
#[doc = "Field `ALL_RESET_FLAG_CLR_PROCPU` writer - clear PRO CPU reset_flag"]
pub type ALL_RESET_FLAG_CLR_PROCPU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ALL_RESET_FLAG_CLR_APPCPU` writer - clear APP CPU reset flag"]
pub type ALL_RESET_FLAG_CLR_APPCPU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OCD_HALT_ON_RESET_APPCPU` reader - APPCPU OcdHaltOnReset"]
pub type OCD_HALT_ON_RESET_APPCPU_R = crate::BitReader;
#[doc = "Field `OCD_HALT_ON_RESET_APPCPU` writer - APPCPU OcdHaltOnReset"]
pub type OCD_HALT_ON_RESET_APPCPU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OCD_HALT_ON_RESET_PROCPU` reader - PROCPU OcdHaltOnReset"]
pub type OCD_HALT_ON_RESET_PROCPU_R = crate::BitReader;
#[doc = "Field `OCD_HALT_ON_RESET_PROCPU` writer - PROCPU OcdHaltOnReset"]
pub type OCD_HALT_ON_RESET_PROCPU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `JTAG_RESET_FLAG_PROCPU` reader - configure jtag reset configure"]
pub type JTAG_RESET_FLAG_PROCPU_R = crate::BitReader;
#[doc = "Field `JTAG_RESET_FLAG_APPCPU` reader - configure jtag reset configure"]
pub type JTAG_RESET_FLAG_APPCPU_R = crate::BitReader;
#[doc = "Field `JTAG_RESET_FLAG_CLR_PROCPU` writer - configure jtag reset configure"]
pub type JTAG_RESET_FLAG_CLR_PROCPU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `JTAG_RESET_FLAG_CLR_APPCPU` writer - configure jtag reset configure"]
pub type JTAG_RESET_FLAG_CLR_APPCPU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DRESET_MASK_APPCPU` reader - configure dreset configure"]
pub type DRESET_MASK_APPCPU_R = crate::BitReader;
#[doc = "Field `DRESET_MASK_APPCPU` writer - configure dreset configure"]
pub type DRESET_MASK_APPCPU_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DRESET_MASK_PROCPU` reader - configure dreset configure"]
pub type DRESET_MASK_PROCPU_R = crate::BitReader;
#[doc = "Field `DRESET_MASK_PROCPU` writer - configure dreset configure"]
pub type DRESET_MASK_PROCPU_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:5 - reset cause of PRO CPU"]
    #[inline(always)]
    pub fn reset_cause_procpu(&self) -> RESET_CAUSE_PROCPU_R {
        RESET_CAUSE_PROCPU_R::new((self.bits & 0x3f) as u8)
    }
    #[doc = "Bits 6:11 - reset cause of APP CPU"]
    #[inline(always)]
    pub fn reset_cause_appcpu(&self) -> RESET_CAUSE_APPCPU_R {
        RESET_CAUSE_APPCPU_R::new(((self.bits >> 6) & 0x3f) as u8)
    }
    #[doc = "Bit 12 - APP CPU state vector sel"]
    #[inline(always)]
    pub fn stat_vector_sel_appcpu(&self) -> STAT_VECTOR_SEL_APPCPU_R {
        STAT_VECTOR_SEL_APPCPU_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - PRO CPU state vector sel"]
    #[inline(always)]
    pub fn stat_vector_sel_procpu(&self) -> STAT_VECTOR_SEL_PROCPU_R {
        STAT_VECTOR_SEL_PROCPU_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - PRO CPU reset_flag"]
    #[inline(always)]
    pub fn all_reset_flag_procpu(&self) -> ALL_RESET_FLAG_PROCPU_R {
        ALL_RESET_FLAG_PROCPU_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - APP CPU reset flag"]
    #[inline(always)]
    pub fn all_reset_flag_appcpu(&self) -> ALL_RESET_FLAG_APPCPU_R {
        ALL_RESET_FLAG_APPCPU_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 18 - APPCPU OcdHaltOnReset"]
    #[inline(always)]
    pub fn ocd_halt_on_reset_appcpu(&self) -> OCD_HALT_ON_RESET_APPCPU_R {
        OCD_HALT_ON_RESET_APPCPU_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - PROCPU OcdHaltOnReset"]
    #[inline(always)]
    pub fn ocd_halt_on_reset_procpu(&self) -> OCD_HALT_ON_RESET_PROCPU_R {
        OCD_HALT_ON_RESET_PROCPU_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - configure jtag reset configure"]
    #[inline(always)]
    pub fn jtag_reset_flag_procpu(&self) -> JTAG_RESET_FLAG_PROCPU_R {
        JTAG_RESET_FLAG_PROCPU_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - configure jtag reset configure"]
    #[inline(always)]
    pub fn jtag_reset_flag_appcpu(&self) -> JTAG_RESET_FLAG_APPCPU_R {
        JTAG_RESET_FLAG_APPCPU_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 24 - configure dreset configure"]
    #[inline(always)]
    pub fn dreset_mask_appcpu(&self) -> DRESET_MASK_APPCPU_R {
        DRESET_MASK_APPCPU_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - configure dreset configure"]
    #[inline(always)]
    pub fn dreset_mask_procpu(&self) -> DRESET_MASK_PROCPU_R {
        DRESET_MASK_PROCPU_R::new(((self.bits >> 25) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RESET_STATE")
            .field("reset_cause_procpu", &self.reset_cause_procpu())
            .field("reset_cause_appcpu", &self.reset_cause_appcpu())
            .field("stat_vector_sel_appcpu", &self.stat_vector_sel_appcpu())
            .field("stat_vector_sel_procpu", &self.stat_vector_sel_procpu())
            .field("all_reset_flag_procpu", &self.all_reset_flag_procpu())
            .field("all_reset_flag_appcpu", &self.all_reset_flag_appcpu())
            .field("ocd_halt_on_reset_appcpu", &self.ocd_halt_on_reset_appcpu())
            .field("ocd_halt_on_reset_procpu", &self.ocd_halt_on_reset_procpu())
            .field("jtag_reset_flag_procpu", &self.jtag_reset_flag_procpu())
            .field("jtag_reset_flag_appcpu", &self.jtag_reset_flag_appcpu())
            .field("dreset_mask_appcpu", &self.dreset_mask_appcpu())
            .field("dreset_mask_procpu", &self.dreset_mask_procpu())
            .finish()
    }
}
impl W {
    #[doc = "Bit 12 - APP CPU state vector sel"]
    #[inline(always)]
    pub fn stat_vector_sel_appcpu(&mut self) -> STAT_VECTOR_SEL_APPCPU_W<'_, RESET_STATE_SPEC> {
        STAT_VECTOR_SEL_APPCPU_W::new(self, 12)
    }
    #[doc = "Bit 13 - PRO CPU state vector sel"]
    #[inline(always)]
    pub fn stat_vector_sel_procpu(&mut self) -> STAT_VECTOR_SEL_PROCPU_W<'_, RESET_STATE_SPEC> {
        STAT_VECTOR_SEL_PROCPU_W::new(self, 13)
    }
    #[doc = "Bit 16 - clear PRO CPU reset_flag"]
    #[inline(always)]
    pub fn all_reset_flag_clr_procpu(
        &mut self,
    ) -> ALL_RESET_FLAG_CLR_PROCPU_W<'_, RESET_STATE_SPEC> {
        ALL_RESET_FLAG_CLR_PROCPU_W::new(self, 16)
    }
    #[doc = "Bit 17 - clear APP CPU reset flag"]
    #[inline(always)]
    pub fn all_reset_flag_clr_appcpu(
        &mut self,
    ) -> ALL_RESET_FLAG_CLR_APPCPU_W<'_, RESET_STATE_SPEC> {
        ALL_RESET_FLAG_CLR_APPCPU_W::new(self, 17)
    }
    #[doc = "Bit 18 - APPCPU OcdHaltOnReset"]
    #[inline(always)]
    pub fn ocd_halt_on_reset_appcpu(&mut self) -> OCD_HALT_ON_RESET_APPCPU_W<'_, RESET_STATE_SPEC> {
        OCD_HALT_ON_RESET_APPCPU_W::new(self, 18)
    }
    #[doc = "Bit 19 - PROCPU OcdHaltOnReset"]
    #[inline(always)]
    pub fn ocd_halt_on_reset_procpu(&mut self) -> OCD_HALT_ON_RESET_PROCPU_W<'_, RESET_STATE_SPEC> {
        OCD_HALT_ON_RESET_PROCPU_W::new(self, 19)
    }
    #[doc = "Bit 22 - configure jtag reset configure"]
    #[inline(always)]
    pub fn jtag_reset_flag_clr_procpu(
        &mut self,
    ) -> JTAG_RESET_FLAG_CLR_PROCPU_W<'_, RESET_STATE_SPEC> {
        JTAG_RESET_FLAG_CLR_PROCPU_W::new(self, 22)
    }
    #[doc = "Bit 23 - configure jtag reset configure"]
    #[inline(always)]
    pub fn jtag_reset_flag_clr_appcpu(
        &mut self,
    ) -> JTAG_RESET_FLAG_CLR_APPCPU_W<'_, RESET_STATE_SPEC> {
        JTAG_RESET_FLAG_CLR_APPCPU_W::new(self, 23)
    }
    #[doc = "Bit 24 - configure dreset configure"]
    #[inline(always)]
    pub fn dreset_mask_appcpu(&mut self) -> DRESET_MASK_APPCPU_W<'_, RESET_STATE_SPEC> {
        DRESET_MASK_APPCPU_W::new(self, 24)
    }
    #[doc = "Bit 25 - configure dreset configure"]
    #[inline(always)]
    pub fn dreset_mask_procpu(&mut self) -> DRESET_MASK_PROCPU_W<'_, RESET_STATE_SPEC> {
        DRESET_MASK_PROCPU_W::new(self, 25)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`reset_state::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`reset_state::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RESET_STATE_SPEC;
impl crate::RegisterSpec for RESET_STATE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`reset_state::R`](R) reader structure"]
impl crate::Readable for RESET_STATE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`reset_state::W`](W) writer structure"]
impl crate::Writable for RESET_STATE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RESET_STATE to value 0x3000"]
impl crate::Resettable for RESET_STATE_SPEC {
    const RESET_VALUE: u32 = 0x3000;
}
