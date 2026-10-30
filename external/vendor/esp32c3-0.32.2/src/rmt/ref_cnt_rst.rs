#[doc = "Register `REF_CNT_RST` writer"]
pub type W = crate::W<REF_CNT_RST_SPEC>;
#[doc = "Field `CH0` writer - reg_ref_cnt_rst_ch0."]
pub type CH0_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH1` writer - reg_ref_cnt_rst_ch1."]
pub type CH1_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH2` writer - reg_ref_cnt_rst_ch2."]
pub type CH2_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH3` writer - reg_ref_cnt_rst_ch3."]
pub type CH3_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<REF_CNT_RST_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - reg_ref_cnt_rst_ch0."]
    #[inline(always)]
    pub fn ch0(&mut self) -> CH0_W<'_, REF_CNT_RST_SPEC> {
        CH0_W::new(self, 0)
    }
    #[doc = "Bit 1 - reg_ref_cnt_rst_ch1."]
    #[inline(always)]
    pub fn ch1(&mut self) -> CH1_W<'_, REF_CNT_RST_SPEC> {
        CH1_W::new(self, 1)
    }
    #[doc = "Bit 2 - reg_ref_cnt_rst_ch2."]
    #[inline(always)]
    pub fn ch2(&mut self) -> CH2_W<'_, REF_CNT_RST_SPEC> {
        CH2_W::new(self, 2)
    }
    #[doc = "Bit 3 - reg_ref_cnt_rst_ch3."]
    #[inline(always)]
    pub fn ch3(&mut self) -> CH3_W<'_, REF_CNT_RST_SPEC> {
        CH3_W::new(self, 3)
    }
}
#[doc = "RMT_REF_CNT_RST_REG.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ref_cnt_rst::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct REF_CNT_RST_SPEC;
impl crate::RegisterSpec for REF_CNT_RST_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`ref_cnt_rst::W`](W) writer structure"]
impl crate::Writable for REF_CNT_RST_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets REF_CNT_RST to value 0"]
impl crate::Resettable for REF_CNT_RST_SPEC {}
