#[doc = "Register `CH1CV` reader"]
pub type R = crate::R<Ch1cvSpec>;
#[doc = "Register `CH1CV` writer"]
pub type W = crate::W<Ch1cvSpec>;
#[doc = "Field `CH1VAL` reader - Capture or compare value of channel1"]
pub type Ch1valR = crate::FieldReader<u32>;
#[doc = "Field `CH1VAL` writer - Capture or compare value of channel1"]
pub type Ch1valW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Capture or compare value of channel1"]
    #[inline(always)]
    pub fn ch1val(&self) -> Ch1valR {
        Ch1valR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - Capture or compare value of channel1"]
    #[inline(always)]
    #[must_use]
    pub fn ch1val(&mut self) -> Ch1valW<Ch1cvSpec> {
        Ch1valW::new(self, 0)
    }
}
#[doc = "Channel 1 capture/compare value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch1cv::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch1cv::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ch1cvSpec;
impl crate::RegisterSpec for Ch1cvSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch1cv::R`](R) reader structure"]
impl crate::Readable for Ch1cvSpec {}
#[doc = "`write(|w| ..)` method takes [`ch1cv::W`](W) writer structure"]
impl crate::Writable for Ch1cvSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CH1CV to value 0"]
impl crate::Resettable for Ch1cvSpec {
    const RESET_VALUE: u32 = 0;
}
