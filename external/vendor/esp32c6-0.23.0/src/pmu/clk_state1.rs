#[doc = "Register `CLK_STATE1` reader"]
pub type R = crate::R<CLK_STATE1_SPEC>;
#[doc = "Field `ICG_FUNC_EN_STATE` reader - need_des"]
pub type ICG_FUNC_EN_STATE_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn icg_func_en_state(&self) -> ICG_FUNC_EN_STATE_R {
        ICG_FUNC_EN_STATE_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CLK_STATE1")
            .field("icg_func_en_state", &self.icg_func_en_state())
            .finish()
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_state1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CLK_STATE1_SPEC;
impl crate::RegisterSpec for CLK_STATE1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`clk_state1::R`](R) reader structure"]
impl crate::Readable for CLK_STATE1_SPEC {}
#[doc = "`reset()` method sets CLK_STATE1 to value 0xffff_ffff"]
impl crate::Resettable for CLK_STATE1_SPEC {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
