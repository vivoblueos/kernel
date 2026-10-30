#[doc = "Register `HP_PERI_TIMEOUT_UID` reader"]
pub type R = crate::R<HP_PERI_TIMEOUT_UID_SPEC>;
#[doc = "Field `HP_PERI_TIMEOUT_UID` reader - Record master id\\[4:0\\] & master permission\\[6:5\\] when trigger timeout. This register will be cleared after the interrupt is cleared."]
pub type HP_PERI_TIMEOUT_UID_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:6 - Record master id\\[4:0\\] & master permission\\[6:5\\] when trigger timeout. This register will be cleared after the interrupt is cleared."]
    #[inline(always)]
    pub fn hp_peri_timeout_uid(&self) -> HP_PERI_TIMEOUT_UID_R {
        HP_PERI_TIMEOUT_UID_R::new((self.bits & 0x7f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HP_PERI_TIMEOUT_UID")
            .field("hp_peri_timeout_uid", &self.hp_peri_timeout_uid())
            .finish()
    }
}
#[doc = "HP_PERI_TIMEOUT_UID register\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_peri_timeout_uid::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_PERI_TIMEOUT_UID_SPEC;
impl crate::RegisterSpec for HP_PERI_TIMEOUT_UID_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hp_peri_timeout_uid::R`](R) reader structure"]
impl crate::Readable for HP_PERI_TIMEOUT_UID_SPEC {}
#[doc = "`reset()` method sets HP_PERI_TIMEOUT_UID to value 0"]
impl crate::Resettable for HP_PERI_TIMEOUT_UID_SPEC {}
