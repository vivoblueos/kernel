#[doc = "Register `RT` reader"]
pub type R = crate::R<RtSpec>;
#[doc = "Register `RT` writer"]
pub type W = crate::W<RtSpec>;
#[doc = "Field `RT` reader - Receiver timeout threshold"]
pub type RtR = crate::FieldReader<u32>;
#[doc = "Field `RT` writer - Receiver timeout threshold"]
pub type RtW<'a, REG> = crate::FieldWriter<'a, REG, 24, u32>;
#[doc = "Field `BL` reader - Block Length"]
pub type BlR = crate::FieldReader;
#[doc = "Field `BL` writer - Block Length"]
pub type BlW<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:23 - Receiver timeout threshold"]
    #[inline(always)]
    pub fn rt(&self) -> RtR {
        RtR::new(self.bits & 0x00ff_ffff)
    }
    #[doc = "Bits 24:31 - Block Length"]
    #[inline(always)]
    pub fn bl(&self) -> BlR {
        BlR::new(((self.bits >> 24) & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:23 - Receiver timeout threshold"]
    #[inline(always)]
    #[must_use]
    pub fn rt(&mut self) -> RtW<RtSpec> {
        RtW::new(self, 0)
    }
    #[doc = "Bits 24:31 - Block Length"]
    #[inline(always)]
    #[must_use]
    pub fn bl(&mut self) -> BlW<RtSpec> {
        BlW::new(self, 24)
    }
}
#[doc = "Receiver timeout register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rt::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rt::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
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
#[doc = "`reset()` method sets RT to value 0"]
impl crate::Resettable for RtSpec {
    const RESET_VALUE: u32 = 0;
}
