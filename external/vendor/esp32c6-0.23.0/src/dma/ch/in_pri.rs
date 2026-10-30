#[doc = "Register `IN_PRI` reader"]
pub type R = crate::R<IN_PRI_SPEC>;
#[doc = "Register `IN_PRI` writer"]
pub type W = crate::W<IN_PRI_SPEC>;
#[doc = "Field `RX_PRI` reader - The priority of Rx channel 0. The larger of the value the higher of the priority."]
pub type RX_PRI_R = crate::FieldReader;
#[doc = "Field `RX_PRI` writer - The priority of Rx channel 0. The larger of the value the higher of the priority."]
pub type RX_PRI_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3 - The priority of Rx channel 0. The larger of the value the higher of the priority."]
    #[inline(always)]
    pub fn rx_pri(&self) -> RX_PRI_R {
        RX_PRI_R::new((self.bits & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IN_PRI")
            .field("rx_pri", &self.rx_pri())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3 - The priority of Rx channel 0. The larger of the value the higher of the priority."]
    #[inline(always)]
    pub fn rx_pri(&mut self) -> RX_PRI_W<'_, IN_PRI_SPEC> {
        RX_PRI_W::new(self, 0)
    }
}
#[doc = "Priority register of Rx channel 0\n\nYou can [`read`](crate::Reg::read) this register and get [`in_pri::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`in_pri::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IN_PRI_SPEC;
impl crate::RegisterSpec for IN_PRI_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`in_pri::R`](R) reader structure"]
impl crate::Readable for IN_PRI_SPEC {}
#[doc = "`write(|w| ..)` method takes [`in_pri::W`](W) writer structure"]
impl crate::Writable for IN_PRI_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IN_PRI to value 0"]
impl crate::Resettable for IN_PRI_SPEC {}
