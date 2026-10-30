#[doc = "Register `BMCMPV` reader"]
pub type R = crate::R<BmcmpvSpec>;
#[doc = "Register `BMCMPV` writer"]
pub type W = crate::W<BmcmpvSpec>;
#[doc = "Field `BMCMPVAL` reader - Bunch mode compare value"]
pub type BmcmpvalR = crate::FieldReader<u16>;
#[doc = "Field `BMCMPVAL` writer - Bunch mode compare value"]
pub type BmcmpvalW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - Bunch mode compare value"]
    #[inline(always)]
    pub fn bmcmpval(&self) -> BmcmpvalR {
        BmcmpvalR::new((self.bits & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - Bunch mode compare value"]
    #[inline(always)]
    #[must_use]
    pub fn bmcmpval(&mut self) -> BmcmpvalW<BmcmpvSpec> {
        BmcmpvalW::new(self, 0)
    }
}
#[doc = "SHRTIMER bunch mode compare value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`bmcmpv::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bmcmpv::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BmcmpvSpec;
impl crate::RegisterSpec for BmcmpvSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`bmcmpv::R`](R) reader structure"]
impl crate::Readable for BmcmpvSpec {}
#[doc = "`write(|w| ..)` method takes [`bmcmpv::W`](W) writer structure"]
impl crate::Writable for BmcmpvSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets BMCMPV to value 0"]
impl crate::Resettable for BmcmpvSpec {
    const RESET_VALUE: u32 = 0;
}
