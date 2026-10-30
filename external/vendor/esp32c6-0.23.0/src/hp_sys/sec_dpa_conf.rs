#[doc = "Register `SEC_DPA_CONF` reader"]
pub type R = crate::R<SEC_DPA_CONF_SPEC>;
#[doc = "Register `SEC_DPA_CONF` writer"]
pub type W = crate::W<SEC_DPA_CONF_SPEC>;
#[doc = "Field `SEC_DPA_LEVEL` reader - 0: anti-DPA disable. 1~3: anti-DPA enable with different security level. The larger the number, the stronger the ability to resist DPA attacks and the higher the security level, but it will increase the computational overhead of the hardware crypto-accelerators. Only avaliable if HP_SYS_SEC_DPA_CFG_SEL is 0."]
pub type SEC_DPA_LEVEL_R = crate::FieldReader;
#[doc = "Field `SEC_DPA_LEVEL` writer - 0: anti-DPA disable. 1~3: anti-DPA enable with different security level. The larger the number, the stronger the ability to resist DPA attacks and the higher the security level, but it will increase the computational overhead of the hardware crypto-accelerators. Only avaliable if HP_SYS_SEC_DPA_CFG_SEL is 0."]
pub type SEC_DPA_LEVEL_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SEC_DPA_CFG_SEL` reader - This field is used to select either HP_SYS_SEC_DPA_LEVEL or EFUSE_SEC_DPA_LEVEL (from efuse) to control dpa_level. 0: EFUSE_SEC_DPA_LEVEL, 1: HP_SYS_SEC_DPA_LEVEL."]
pub type SEC_DPA_CFG_SEL_R = crate::BitReader;
#[doc = "Field `SEC_DPA_CFG_SEL` writer - This field is used to select either HP_SYS_SEC_DPA_LEVEL or EFUSE_SEC_DPA_LEVEL (from efuse) to control dpa_level. 0: EFUSE_SEC_DPA_LEVEL, 1: HP_SYS_SEC_DPA_LEVEL."]
pub type SEC_DPA_CFG_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:1 - 0: anti-DPA disable. 1~3: anti-DPA enable with different security level. The larger the number, the stronger the ability to resist DPA attacks and the higher the security level, but it will increase the computational overhead of the hardware crypto-accelerators. Only avaliable if HP_SYS_SEC_DPA_CFG_SEL is 0."]
    #[inline(always)]
    pub fn sec_dpa_level(&self) -> SEC_DPA_LEVEL_R {
        SEC_DPA_LEVEL_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bit 2 - This field is used to select either HP_SYS_SEC_DPA_LEVEL or EFUSE_SEC_DPA_LEVEL (from efuse) to control dpa_level. 0: EFUSE_SEC_DPA_LEVEL, 1: HP_SYS_SEC_DPA_LEVEL."]
    #[inline(always)]
    pub fn sec_dpa_cfg_sel(&self) -> SEC_DPA_CFG_SEL_R {
        SEC_DPA_CFG_SEL_R::new(((self.bits >> 2) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SEC_DPA_CONF")
            .field("sec_dpa_level", &self.sec_dpa_level())
            .field("sec_dpa_cfg_sel", &self.sec_dpa_cfg_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:1 - 0: anti-DPA disable. 1~3: anti-DPA enable with different security level. The larger the number, the stronger the ability to resist DPA attacks and the higher the security level, but it will increase the computational overhead of the hardware crypto-accelerators. Only avaliable if HP_SYS_SEC_DPA_CFG_SEL is 0."]
    #[inline(always)]
    pub fn sec_dpa_level(&mut self) -> SEC_DPA_LEVEL_W<'_, SEC_DPA_CONF_SPEC> {
        SEC_DPA_LEVEL_W::new(self, 0)
    }
    #[doc = "Bit 2 - This field is used to select either HP_SYS_SEC_DPA_LEVEL or EFUSE_SEC_DPA_LEVEL (from efuse) to control dpa_level. 0: EFUSE_SEC_DPA_LEVEL, 1: HP_SYS_SEC_DPA_LEVEL."]
    #[inline(always)]
    pub fn sec_dpa_cfg_sel(&mut self) -> SEC_DPA_CFG_SEL_W<'_, SEC_DPA_CONF_SPEC> {
        SEC_DPA_CFG_SEL_W::new(self, 2)
    }
}
#[doc = "HP anti-DPA security configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sec_dpa_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sec_dpa_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SEC_DPA_CONF_SPEC;
impl crate::RegisterSpec for SEC_DPA_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sec_dpa_conf::R`](R) reader structure"]
impl crate::Readable for SEC_DPA_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sec_dpa_conf::W`](W) writer structure"]
impl crate::Writable for SEC_DPA_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SEC_DPA_CONF to value 0"]
impl crate::Resettable for SEC_DPA_CONF_SPEC {}
