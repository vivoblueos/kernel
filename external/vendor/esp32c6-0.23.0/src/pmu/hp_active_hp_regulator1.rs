#[doc = "Register `HP_ACTIVE_HP_REGULATOR1` reader"]
pub type R = crate::R<HP_ACTIVE_HP_REGULATOR1_SPEC>;
#[doc = "Register `HP_ACTIVE_HP_REGULATOR1` writer"]
pub type W = crate::W<HP_ACTIVE_HP_REGULATOR1_SPEC>;
#[doc = "Field `HP_ACTIVE_HP_REGULATOR_DRV_B` reader - need_des"]
pub type HP_ACTIVE_HP_REGULATOR_DRV_B_R = crate::FieldReader<u32>;
#[doc = "Field `HP_ACTIVE_HP_REGULATOR_DRV_B` writer - need_des"]
pub type HP_ACTIVE_HP_REGULATOR_DRV_B_W<'a, REG> = crate::FieldWriter<'a, REG, 24, u32>;
impl R {
    #[doc = "Bits 8:31 - need_des"]
    #[inline(always)]
    pub fn hp_active_hp_regulator_drv_b(&self) -> HP_ACTIVE_HP_REGULATOR_DRV_B_R {
        HP_ACTIVE_HP_REGULATOR_DRV_B_R::new((self.bits >> 8) & 0x00ff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HP_ACTIVE_HP_REGULATOR1")
            .field(
                "hp_active_hp_regulator_drv_b",
                &self.hp_active_hp_regulator_drv_b(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 8:31 - need_des"]
    #[inline(always)]
    pub fn hp_active_hp_regulator_drv_b(
        &mut self,
    ) -> HP_ACTIVE_HP_REGULATOR_DRV_B_W<'_, HP_ACTIVE_HP_REGULATOR1_SPEC> {
        HP_ACTIVE_HP_REGULATOR_DRV_B_W::new(self, 8)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_active_hp_regulator1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hp_active_hp_regulator1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_ACTIVE_HP_REGULATOR1_SPEC;
impl crate::RegisterSpec for HP_ACTIVE_HP_REGULATOR1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hp_active_hp_regulator1::R`](R) reader structure"]
impl crate::Readable for HP_ACTIVE_HP_REGULATOR1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`hp_active_hp_regulator1::W`](W) writer structure"]
impl crate::Writable for HP_ACTIVE_HP_REGULATOR1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HP_ACTIVE_HP_REGULATOR1 to value 0"]
impl crate::Resettable for HP_ACTIVE_HP_REGULATOR1_SPEC {}
