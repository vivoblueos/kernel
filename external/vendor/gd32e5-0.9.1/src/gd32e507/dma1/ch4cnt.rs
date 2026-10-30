#[doc = "Register `CH4CNT` reader"]
pub type R = crate::R<Ch4cntSpec>;
#[doc = "Register `CH4CNT` writer"]
pub type W = crate::W<Ch4cntSpec>;
#[doc = "Field `CNT` reader - Transfer counter"]
pub type CntR = crate::FieldReader<u16>;
#[doc = "Field `CNT` writer - Transfer counter"]
pub type CntW<'a, REG> = crate::FieldWriterSafe<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - Transfer counter"]
    #[inline(always)]
    pub fn cnt(&self) -> CntR {
        CntR::new((self.bits & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - Transfer counter"]
    #[inline(always)]
    #[must_use]
    pub fn cnt(&mut self) -> CntW<Ch4cntSpec> {
        CntW::new(self, 0)
    }
}
#[doc = "Channel 4 counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch4cnt::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch4cnt::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ch4cntSpec;
impl crate::RegisterSpec for Ch4cntSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch4cnt::R`](R) reader structure"]
impl crate::Readable for Ch4cntSpec {}
#[doc = "`write(|w| ..)` method takes [`ch4cnt::W`](W) writer structure"]
impl crate::Writable for Ch4cntSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CH4CNT to value 0"]
impl crate::Resettable for Ch4cntSpec {
    const RESET_VALUE: u32 = 0;
}
