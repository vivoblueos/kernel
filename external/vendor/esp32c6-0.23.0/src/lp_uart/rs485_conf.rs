#[doc = "Register `RS485_CONF` reader"]
pub type R = crate::R<RS485_CONF_SPEC>;
#[doc = "Register `RS485_CONF` writer"]
pub type W = crate::W<RS485_CONF_SPEC>;
#[doc = "Field `DL0_EN` reader - Set this bit to delay the stop bit by 1 bit."]
pub type DL0_EN_R = crate::BitReader;
#[doc = "Field `DL0_EN` writer - Set this bit to delay the stop bit by 1 bit."]
pub type DL0_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DL1_EN` reader - Set this bit to delay the stop bit by 1 bit."]
pub type DL1_EN_R = crate::BitReader;
#[doc = "Field `DL1_EN` writer - Set this bit to delay the stop bit by 1 bit."]
pub type DL1_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 1 - Set this bit to delay the stop bit by 1 bit."]
    #[inline(always)]
    pub fn dl0_en(&self) -> DL0_EN_R {
        DL0_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Set this bit to delay the stop bit by 1 bit."]
    #[inline(always)]
    pub fn dl1_en(&self) -> DL1_EN_R {
        DL1_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RS485_CONF")
            .field("dl0_en", &self.dl0_en())
            .field("dl1_en", &self.dl1_en())
            .finish()
    }
}
impl W {
    #[doc = "Bit 1 - Set this bit to delay the stop bit by 1 bit."]
    #[inline(always)]
    pub fn dl0_en(&mut self) -> DL0_EN_W<'_, RS485_CONF_SPEC> {
        DL0_EN_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set this bit to delay the stop bit by 1 bit."]
    #[inline(always)]
    pub fn dl1_en(&mut self) -> DL1_EN_W<'_, RS485_CONF_SPEC> {
        DL1_EN_W::new(self, 2)
    }
}
#[doc = "RS485 mode configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`rs485_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rs485_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RS485_CONF_SPEC;
impl crate::RegisterSpec for RS485_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rs485_conf::R`](R) reader structure"]
impl crate::Readable for RS485_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`rs485_conf::W`](W) writer structure"]
impl crate::Writable for RS485_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RS485_CONF to value 0"]
impl crate::Resettable for RS485_CONF_SPEC {}
