#[doc = "Register `OUT_PRI` reader"]
pub type R = crate::R<OUT_PRI_SPEC>;
#[doc = "Register `OUT_PRI` writer"]
pub type W = crate::W<OUT_PRI_SPEC>;
#[doc = "Field `TX_PRI` reader - The priority of Tx channel 0. The larger of the value the higher of the priority."]
pub type TX_PRI_R = crate::FieldReader;
#[doc = "Field `TX_PRI` writer - The priority of Tx channel 0. The larger of the value the higher of the priority."]
pub type TX_PRI_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3 - The priority of Tx channel 0. The larger of the value the higher of the priority."]
    #[inline(always)]
    pub fn tx_pri(&self) -> TX_PRI_R {
        TX_PRI_R::new((self.bits & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("OUT_PRI")
            .field("tx_pri", &self.tx_pri())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3 - The priority of Tx channel 0. The larger of the value the higher of the priority."]
    #[inline(always)]
    pub fn tx_pri(&mut self) -> TX_PRI_W<'_, OUT_PRI_SPEC> {
        TX_PRI_W::new(self, 0)
    }
}
#[doc = "Priority register of Tx channel 0.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_pri::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_pri::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OUT_PRI_SPEC;
impl crate::RegisterSpec for OUT_PRI_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`out_pri::R`](R) reader structure"]
impl crate::Readable for OUT_PRI_SPEC {}
#[doc = "`write(|w| ..)` method takes [`out_pri::W`](W) writer structure"]
impl crate::Writable for OUT_PRI_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets OUT_PRI to value 0"]
impl crate::Resettable for OUT_PRI_SPEC {}
