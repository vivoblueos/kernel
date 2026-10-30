#[doc = "Register `HP_PERI_TIMEOUT_ADDR` reader"]
pub type R = crate::R<HP_PERI_TIMEOUT_ADDR_SPEC>;
#[doc = "Field `HP_PERI_TIMEOUT_ADDR` reader - Record the address information of abnormal access"]
pub type HP_PERI_TIMEOUT_ADDR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Record the address information of abnormal access"]
    #[inline(always)]
    pub fn hp_peri_timeout_addr(&self) -> HP_PERI_TIMEOUT_ADDR_R {
        HP_PERI_TIMEOUT_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("HP_PERI_TIMEOUT_ADDR")
            .field("hp_peri_timeout_addr", &self.hp_peri_timeout_addr())
            .finish()
    }
}
#[doc = "HP_PERI_TIMEOUT_ADDR register\n\nYou can [`read`](crate::Reg::read) this register and get [`hp_peri_timeout_addr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HP_PERI_TIMEOUT_ADDR_SPEC;
impl crate::RegisterSpec for HP_PERI_TIMEOUT_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hp_peri_timeout_addr::R`](R) reader structure"]
impl crate::Readable for HP_PERI_TIMEOUT_ADDR_SPEC {}
#[doc = "`reset()` method sets HP_PERI_TIMEOUT_ADDR to value 0"]
impl crate::Resettable for HP_PERI_TIMEOUT_ADDR_SPEC {}
