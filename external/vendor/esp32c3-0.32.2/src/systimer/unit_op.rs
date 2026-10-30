#[doc = "Register `UNIT%s_OP` reader"]
pub type R = crate::R<UNIT_OP_SPEC>;
#[doc = "Register `UNIT%s_OP` writer"]
pub type W = crate::W<UNIT_OP_SPEC>;
#[doc = "Field `VALUE_VALID` reader - reg_timer_unit0_value_valid"]
pub type VALUE_VALID_R = crate::BitReader;
#[doc = "Field `UPDATE` writer - update timer_unit0"]
pub type UPDATE_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 29 - reg_timer_unit0_value_valid"]
    #[inline(always)]
    pub fn value_valid(&self) -> VALUE_VALID_R {
        VALUE_VALID_R::new(((self.bits >> 29) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("UNIT_OP")
            .field("value_valid", &self.value_valid())
            .finish()
    }
}
impl W {
    #[doc = "Bit 30 - update timer_unit0"]
    #[inline(always)]
    pub fn update(&mut self) -> UPDATE_W<'_, UNIT_OP_SPEC> {
        UPDATE_W::new(self, 30)
    }
}
#[doc = "SYSTIMER_UNIT%s_OP.\n\nYou can [`read`](crate::Reg::read) this register and get [`unit_op::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`unit_op::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct UNIT_OP_SPEC;
impl crate::RegisterSpec for UNIT_OP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`unit_op::R`](R) reader structure"]
impl crate::Readable for UNIT_OP_SPEC {}
#[doc = "`write(|w| ..)` method takes [`unit_op::W`](W) writer structure"]
impl crate::Writable for UNIT_OP_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets UNIT%s_OP to value 0"]
impl crate::Resettable for UNIT_OP_SPEC {}
