#[doc = "Register `MAC_HLL` reader"]
pub type R = crate::R<MacHllSpec>;
#[doc = "Register `MAC_HLL` writer"]
pub type W = crate::W<MacHllSpec>;
#[doc = "Field `HLL` reader - Hash list low"]
pub type HllR = crate::FieldReader<u32>;
#[doc = "Field `HLL` writer - Hash list low"]
pub type HllW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Hash list low"]
    #[inline(always)]
    pub fn hll(&self) -> HllR {
        HllR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - Hash list low"]
    #[inline(always)]
    #[must_use]
    pub fn hll(&mut self) -> HllW<MacHllSpec> {
        HllW::new(self, 0)
    }
}
#[doc = "Ethernet MAC hash list low register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_hll::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mac_hll::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacHllSpec;
impl crate::RegisterSpec for MacHllSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_hll::R`](R) reader structure"]
impl crate::Readable for MacHllSpec {}
#[doc = "`write(|w| ..)` method takes [`mac_hll::W`](W) writer structure"]
impl crate::Writable for MacHllSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets MAC_HLL to value 0"]
impl crate::Resettable for MacHllSpec {
    const RESET_VALUE: u32 = 0;
}
