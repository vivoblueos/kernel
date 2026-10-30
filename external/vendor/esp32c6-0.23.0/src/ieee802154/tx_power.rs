#[doc = "Register `TX_POWER` reader"]
pub type R = crate::R<TX_POWER_SPEC>;
#[doc = "Register `TX_POWER` writer"]
pub type W = crate::W<TX_POWER_SPEC>;
#[doc = "Field `TX_POWER` reader - "]
pub type TX_POWER_R = crate::FieldReader;
#[doc = "Field `TX_POWER` writer - "]
pub type TX_POWER_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
impl R {
    #[doc = "Bits 0:4"]
    #[inline(always)]
    pub fn tx_power(&self) -> TX_POWER_R {
        TX_POWER_R::new((self.bits & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_POWER")
            .field("tx_power", &self.tx_power())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:4"]
    #[inline(always)]
    pub fn tx_power(&mut self) -> TX_POWER_W<'_, TX_POWER_SPEC> {
        TX_POWER_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_power::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_power::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_POWER_SPEC;
impl crate::RegisterSpec for TX_POWER_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_power::R`](R) reader structure"]
impl crate::Readable for TX_POWER_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_power::W`](W) writer structure"]
impl crate::Writable for TX_POWER_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_POWER to value 0"]
impl crate::Resettable for TX_POWER_SPEC {}
