#[doc = "Register `MEM_TEST_CONF` reader"]
pub type R = crate::R<MEM_TEST_CONF_SPEC>;
#[doc = "Register `MEM_TEST_CONF` writer"]
pub type W = crate::W<MEM_TEST_CONF_SPEC>;
#[doc = "Field `HP_MEM_WPULSE` reader - This field controls hp system memory WPULSE parameter."]
pub type HP_MEM_WPULSE_R = crate::FieldReader;
#[doc = "Field `HP_MEM_WPULSE` writer - This field controls hp system memory WPULSE parameter."]
pub type HP_MEM_WPULSE_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `HP_MEM_WA` reader - This field controls hp system memory WA parameter."]
pub type HP_MEM_WA_R = crate::FieldReader;
#[doc = "Field `HP_MEM_WA` writer - This field controls hp system memory WA parameter."]
pub type HP_MEM_WA_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `HP_MEM_RA` reader - This field controls hp system memory RA parameter."]
pub type HP_MEM_RA_R = crate::FieldReader;
#[doc = "Field `HP_MEM_RA` writer - This field controls hp system memory RA parameter."]
pub type HP_MEM_RA_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:2 - This field controls hp system memory WPULSE parameter."]
    #[inline(always)]
    pub fn hp_mem_wpulse(&self) -> HP_MEM_WPULSE_R {
        HP_MEM_WPULSE_R::new((self.bits & 7) as u8)
    }
    #[doc = "Bits 3:5 - This field controls hp system memory WA parameter."]
    #[inline(always)]
    pub fn hp_mem_wa(&self) -> HP_MEM_WA_R {
        HP_MEM_WA_R::new(((self.bits >> 3) & 7) as u8)
    }
    #[doc = "Bits 6:7 - This field controls hp system memory RA parameter."]
    #[inline(always)]
    pub fn hp_mem_ra(&self) -> HP_MEM_RA_R {
        HP_MEM_RA_R::new(((self.bits >> 6) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MEM_TEST_CONF")
            .field("hp_mem_wpulse", &self.hp_mem_wpulse())
            .field("hp_mem_wa", &self.hp_mem_wa())
            .field("hp_mem_ra", &self.hp_mem_ra())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:2 - This field controls hp system memory WPULSE parameter."]
    #[inline(always)]
    pub fn hp_mem_wpulse(&mut self) -> HP_MEM_WPULSE_W<'_, MEM_TEST_CONF_SPEC> {
        HP_MEM_WPULSE_W::new(self, 0)
    }
    #[doc = "Bits 3:5 - This field controls hp system memory WA parameter."]
    #[inline(always)]
    pub fn hp_mem_wa(&mut self) -> HP_MEM_WA_W<'_, MEM_TEST_CONF_SPEC> {
        HP_MEM_WA_W::new(self, 3)
    }
    #[doc = "Bits 6:7 - This field controls hp system memory RA parameter."]
    #[inline(always)]
    pub fn hp_mem_ra(&mut self) -> HP_MEM_RA_W<'_, MEM_TEST_CONF_SPEC> {
        HP_MEM_RA_W::new(self, 6)
    }
}
#[doc = "MEM_TEST configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_test_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_test_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MEM_TEST_CONF_SPEC;
impl crate::RegisterSpec for MEM_TEST_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mem_test_conf::R`](R) reader structure"]
impl crate::Readable for MEM_TEST_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`mem_test_conf::W`](W) writer structure"]
impl crate::Writable for MEM_TEST_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MEM_TEST_CONF to value 0x20"]
impl crate::Resettable for MEM_TEST_CONF_SPEC {
    const RESET_VALUE: u32 = 0x20;
}
