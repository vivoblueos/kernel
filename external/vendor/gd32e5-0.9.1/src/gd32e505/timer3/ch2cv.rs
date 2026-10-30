#[doc = "Register `CH2CV` reader"]
pub type R = crate::R<Ch2cvSpec>;
#[doc = "Register `CH2CV` writer"]
pub type W = crate::W<Ch2cvSpec>;
#[doc = "Field `CH2VAL` reader - Capture or compare value of channel 2"]
pub type Ch2valR = crate::FieldReader<u16>;
#[doc = "Field `CH2VAL` writer - Capture or compare value of channel 2"]
pub type Ch2valW<'a, REG> = crate::FieldWriterSafe<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - Capture or compare value of channel 2"]
    #[inline(always)]
    pub fn ch2val(&self) -> Ch2valR {
        Ch2valR::new((self.bits & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - Capture or compare value of channel 2"]
    #[inline(always)]
    #[must_use]
    pub fn ch2val(&mut self) -> Ch2valW<Ch2cvSpec> {
        Ch2valW::new(self, 0)
    }
}
#[doc = "Channel 2 capture/compare value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch2cv::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch2cv::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ch2cvSpec;
impl crate::RegisterSpec for Ch2cvSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch2cv::R`](R) reader structure"]
impl crate::Readable for Ch2cvSpec {}
#[doc = "`write(|w| ..)` method takes [`ch2cv::W`](W) writer structure"]
impl crate::Writable for Ch2cvSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CH2CV to value 0"]
impl crate::Resettable for Ch2cvSpec {
    const RESET_VALUE: u32 = 0;
}
