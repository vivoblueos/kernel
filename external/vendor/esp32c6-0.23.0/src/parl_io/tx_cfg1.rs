#[doc = "Register `TX_CFG1` reader"]
pub type R = crate::R<TX_CFG1_SPEC>;
#[doc = "Register `TX_CFG1` writer"]
pub type W = crate::W<TX_CFG1_SPEC>;
#[doc = "Field `TX_IDLE_VALUE` reader - Configures data value on tx bus when IDLE state."]
pub type TX_IDLE_VALUE_R = crate::FieldReader<u16>;
#[doc = "Field `TX_IDLE_VALUE` writer - Configures data value on tx bus when IDLE state."]
pub type TX_IDLE_VALUE_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 16:31 - Configures data value on tx bus when IDLE state."]
    #[inline(always)]
    pub fn tx_idle_value(&self) -> TX_IDLE_VALUE_R {
        TX_IDLE_VALUE_R::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TX_CFG1")
            .field("tx_idle_value", &self.tx_idle_value())
            .finish()
    }
}
impl W {
    #[doc = "Bits 16:31 - Configures data value on tx bus when IDLE state."]
    #[inline(always)]
    pub fn tx_idle_value(&mut self) -> TX_IDLE_VALUE_W<'_, TX_CFG1_SPEC> {
        TX_IDLE_VALUE_W::new(self, 16)
    }
}
#[doc = "Parallel TX module configuration register1.\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_cfg1::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_cfg1::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TX_CFG1_SPEC;
impl crate::RegisterSpec for TX_CFG1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tx_cfg1::R`](R) reader structure"]
impl crate::Readable for TX_CFG1_SPEC {}
#[doc = "`write(|w| ..)` method takes [`tx_cfg1::W`](W) writer structure"]
impl crate::Writable for TX_CFG1_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TX_CFG1 to value 0"]
impl crate::Resettable for TX_CFG1_SPEC {}
