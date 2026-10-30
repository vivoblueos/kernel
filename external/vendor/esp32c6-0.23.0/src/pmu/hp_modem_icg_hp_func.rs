#[doc = "Register `HP_MODEM_ICG_HP_FUNC` reader"]
pub type R = crate::R<HP_MODEM_ICG_HP_FUNC_SPEC>;
#[doc = "Register `HP_MODEM_ICG_HP_FUNC` writer"]
pub type W = crate::W<HP_MODEM_ICG_HP_FUNC_SPEC>;
#[doc = "Field `HP_MODEM_DIG_ICG_FUNC_EN` reader - need_des"]
pub type HP_MODEM_DIG_ICG_FUNC_EN_R = crate::FieldReader<u32>;
#[doc = "Field `HP_MODEM_DIG_ICG_FUNC_EN` writer - need_des"]
pub type HP_MODEM_DIG_ICG_FUNC_EN_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn hp_modem_dig_icg_func_en(&self) -> HP_MODEM_DIG_ICG_FUNC_EN_R {
        HP_MODEM_DIG_ICG_FUNC_EN_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HP_MODEM_ICG_HP_FUNC")
            .field("hp_modem_dig_icg_func_en", &self.hp_modem_dig_icg_func_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn hp_modem_dig_icg_func_en(
        &mut self,
    ) -> HP_MODEM_DIG_ICG_FUNC_EN_W<'_, HP_MODEM_ICG_HP_FUNC_SPEC> {
        HP_MODEM_DIG_ICG_FUNC_EN_W::new(self, 0)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_modem_icg_hp_func::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hp_modem_icg_hp_func::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_MODEM_ICG_HP_FUNC_SPEC;
impl crate::RegisterSpec for HP_MODEM_ICG_HP_FUNC_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hp_modem_icg_hp_func::R`](R) reader structure"]
impl crate::Readable for HP_MODEM_ICG_HP_FUNC_SPEC {}
#[doc = "`write(|w| ..)` method takes [`hp_modem_icg_hp_func::W`](W) writer structure"]
impl crate::Writable for HP_MODEM_ICG_HP_FUNC_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets HP_MODEM_ICG_HP_FUNC to value 0xffff_ffff"]
impl crate::Resettable for HP_MODEM_ICG_HP_FUNC_SPEC {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
