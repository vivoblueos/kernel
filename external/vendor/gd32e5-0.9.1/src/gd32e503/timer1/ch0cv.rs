#[doc = "Register `CH0CV` reader"]
pub type R = crate::R<Ch0cvSpec>;
#[doc = "Register `CH0CV` writer"]
pub type W = crate::W<Ch0cvSpec>;
#[doc = "Field `CH0VAL` reader - Capture or compare value of channel 0"]
pub type Ch0valR = crate::FieldReader<u32>;
#[doc = "Field `CH0VAL` writer - Capture or compare value of channel 0"]
pub type Ch0valW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Capture or compare value of channel 0"]
    #[inline(always)]
    pub fn ch0val(&self) -> Ch0valR {
        Ch0valR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - Capture or compare value of channel 0"]
    #[inline(always)]
    #[must_use]
    pub fn ch0val(&mut self) -> Ch0valW<Ch0cvSpec> {
        Ch0valW::new(self, 0)
    }
}
#[doc = "Channel 0 capture/compare value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch0cv::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch0cv::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ch0cvSpec;
impl crate::RegisterSpec for Ch0cvSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch0cv::R`](R) reader structure"]
impl crate::Readable for Ch0cvSpec {}
#[doc = "`write(|w| ..)` method takes [`ch0cv::W`](W) writer structure"]
impl crate::Writable for Ch0cvSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CH0CV to value 0"]
impl crate::Resettable for Ch0cvSpec {
    const RESET_VALUE: u32 = 0;
}
