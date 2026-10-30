#[doc = "Register `RLD` reader"]
pub type R = crate::R<RldSpec>;
#[doc = "Register `RLD` writer"]
pub type W = crate::W<RldSpec>;
#[doc = "Field `RLD` reader - Free watchdog timer counter reload value"]
pub type RldR = crate::FieldReader<u16>;
#[doc = "Field `RLD` writer - Free watchdog timer counter reload value"]
pub type RldW<'a, REG> = crate::FieldWriterSafe<'a, REG, 12, u16>;
impl R {
    #[doc = "Bits 0:11 - Free watchdog timer counter reload value"]
    #[inline(always)]
    pub fn rld(&self) -> RldR {
        RldR::new((self.bits & 0x0fff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:11 - Free watchdog timer counter reload value"]
    #[inline(always)]
    #[must_use]
    pub fn rld(&mut self) -> RldW<RldSpec> {
        RldW::new(self, 0)
    }
}
#[doc = "Reload register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rld::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rld::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RldSpec;
impl crate::RegisterSpec for RldSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rld::R`](R) reader structure"]
impl crate::Readable for RldSpec {}
#[doc = "`write(|w| ..)` method takes [`rld::W`](W) writer structure"]
impl crate::Writable for RldSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets RLD to value 0x0fff"]
impl crate::Resettable for RldSpec {
    const RESET_VALUE: u32 = 0x0fff;
}
