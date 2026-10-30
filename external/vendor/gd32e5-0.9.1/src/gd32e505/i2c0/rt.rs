#[doc = "Register `RT` reader"]
pub type R = crate::R<RtSpec>;
#[doc = "Register `RT` writer"]
pub type W = crate::W<RtSpec>;
#[doc = "Field `RISETIME` reader - Maximum rise time in master mode"]
pub type RisetimeR = crate::FieldReader;
#[doc = "Field `RISETIME` writer - Maximum rise time in master mode"]
pub type RisetimeW<'a, REG> = crate::FieldWriter<'a, REG, 7>;
impl R {
    #[doc = "Bits 0:6 - Maximum rise time in master mode"]
    #[inline(always)]
    pub fn risetime(&self) -> RisetimeR {
        RisetimeR::new((self.bits & 0x7f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:6 - Maximum rise time in master mode"]
    #[inline(always)]
    #[must_use]
    pub fn risetime(&mut self) -> RisetimeW<RtSpec> {
        RisetimeW::new(self, 0)
    }
}
#[doc = "Rise time register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rt::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rt::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RtSpec;
impl crate::RegisterSpec for RtSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rt::R`](R) reader structure"]
impl crate::Readable for RtSpec {}
#[doc = "`write(|w| ..)` method takes [`rt::W`](W) writer structure"]
impl crate::Writable for RtSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets RT to value 0x02"]
impl crate::Resettable for RtSpec {
    const RESET_VALUE: u32 = 0x02;
}
