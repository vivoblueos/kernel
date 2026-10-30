#[doc = "Register `CONF0` reader"]
pub type R = crate::R<CONF0_SPEC>;
#[doc = "Register `CONF0` writer"]
pub type W = crate::W<CONF0_SPEC>;
#[doc = "Field `TIMER_SEL` reader - reg_timer_sel_lsch0."]
pub type TIMER_SEL_R = crate::FieldReader;
#[doc = "Field `TIMER_SEL` writer - reg_timer_sel_lsch0."]
pub type TIMER_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SIG_OUT_EN` reader - reg_sig_out_en_lsch0."]
pub type SIG_OUT_EN_R = crate::BitReader;
#[doc = "Field `SIG_OUT_EN` writer - reg_sig_out_en_lsch0."]
pub type SIG_OUT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IDLE_LV` reader - reg_idle_lv_lsch0."]
pub type IDLE_LV_R = crate::BitReader;
#[doc = "Field `IDLE_LV` writer - reg_idle_lv_lsch0."]
pub type IDLE_LV_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PARA_UP` writer - reg_para_up_lsch0."]
pub type PARA_UP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OVF_NUM` reader - reg_ovf_num_lsch0."]
pub type OVF_NUM_R = crate::FieldReader<u16>;
#[doc = "Field `OVF_NUM` writer - reg_ovf_num_lsch0."]
pub type OVF_NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `OVF_CNT_EN` reader - reg_ovf_cnt_en_lsch0."]
pub type OVF_CNT_EN_R = crate::BitReader;
#[doc = "Field `OVF_CNT_EN` writer - reg_ovf_cnt_en_lsch0."]
pub type OVF_CNT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OVF_CNT_RESET` writer - reg_ovf_cnt_reset_lsch0."]
pub type OVF_CNT_RESET_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:1 - reg_timer_sel_lsch0."]
    #[inline(always)]
    pub fn timer_sel(&self) -> TIMER_SEL_R {
        TIMER_SEL_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bit 2 - reg_sig_out_en_lsch0."]
    #[inline(always)]
    pub fn sig_out_en(&self) -> SIG_OUT_EN_R {
        SIG_OUT_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - reg_idle_lv_lsch0."]
    #[inline(always)]
    pub fn idle_lv(&self) -> IDLE_LV_R {
        IDLE_LV_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 5:14 - reg_ovf_num_lsch0."]
    #[inline(always)]
    pub fn ovf_num(&self) -> OVF_NUM_R {
        OVF_NUM_R::new(((self.bits >> 5) & 0x03ff) as u16)
    }
    #[doc = "Bit 15 - reg_ovf_cnt_en_lsch0."]
    #[inline(always)]
    pub fn ovf_cnt_en(&self) -> OVF_CNT_EN_R {
        OVF_CNT_EN_R::new(((self.bits >> 15) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CONF0")
            .field("timer_sel", &self.timer_sel())
            .field("sig_out_en", &self.sig_out_en())
            .field("idle_lv", &self.idle_lv())
            .field("ovf_num", &self.ovf_num())
            .field("ovf_cnt_en", &self.ovf_cnt_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - reg_timer_sel_lsch0."]
    #[inline(always)]
    pub fn timer_sel(&mut self) -> TIMER_SEL_W<'_, CONF0_SPEC> {
        TIMER_SEL_W::new(self, 0)
    }
    #[doc = "Bit 2 - reg_sig_out_en_lsch0."]
    #[inline(always)]
    pub fn sig_out_en(&mut self) -> SIG_OUT_EN_W<'_, CONF0_SPEC> {
        SIG_OUT_EN_W::new(self, 2)
    }
    #[doc = "Bit 3 - reg_idle_lv_lsch0."]
    #[inline(always)]
    pub fn idle_lv(&mut self) -> IDLE_LV_W<'_, CONF0_SPEC> {
        IDLE_LV_W::new(self, 3)
    }
    #[doc = "Bit 4 - reg_para_up_lsch0."]
    #[inline(always)]
    pub fn para_up(&mut self) -> PARA_UP_W<'_, CONF0_SPEC> {
        PARA_UP_W::new(self, 4)
    }
    #[doc = "Bits 5:14 - reg_ovf_num_lsch0."]
    #[inline(always)]
    pub fn ovf_num(&mut self) -> OVF_NUM_W<'_, CONF0_SPEC> {
        OVF_NUM_W::new(self, 5)
    }
    #[doc = "Bit 15 - reg_ovf_cnt_en_lsch0."]
    #[inline(always)]
    pub fn ovf_cnt_en(&mut self) -> OVF_CNT_EN_W<'_, CONF0_SPEC> {
        OVF_CNT_EN_W::new(self, 15)
    }
    #[doc = "Bit 16 - reg_ovf_cnt_reset_lsch0."]
    #[inline(always)]
    pub fn ovf_cnt_reset(&mut self) -> OVF_CNT_RESET_W<'_, CONF0_SPEC> {
        OVF_CNT_RESET_W::new(self, 16)
    }
}
#[doc = "LEDC_LSCH0_CONF0.\n\nYou can [`read`](crate::Reg::read) this register and get [`conf0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CONF0_SPEC;
impl crate::RegisterSpec for CONF0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`conf0::R`](R) reader structure"]
impl crate::Readable for CONF0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`conf0::W`](W) writer structure"]
impl crate::Writable for CONF0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CONF0 to value 0"]
impl crate::Resettable for CONF0_SPEC {}
