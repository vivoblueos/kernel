#[doc = "Register `DIEP0LEN` reader"]
pub type R = crate::R<Diep0lenSpec>;
#[doc = "Register `DIEP0LEN` writer"]
pub type W = crate::W<Diep0lenSpec>;
#[doc = "Field `TLEN` reader - Transfer length"]
pub type TlenR = crate::FieldReader;
#[doc = "Field `TLEN` writer - Transfer length"]
pub type TlenW<'a, REG> = crate::FieldWriter<'a, REG, 7>;
#[doc = "Field `PCNT` reader - Packet count"]
pub type PcntR = crate::FieldReader;
#[doc = "Field `PCNT` writer - Packet count"]
pub type PcntW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:6 - Transfer length"]
    #[inline(always)]
    pub fn tlen(&self) -> TlenR {
        TlenR::new((self.bits & 0x7f) as u8)
    }
    #[doc = "Bits 19:20 - Packet count"]
    #[inline(always)]
    pub fn pcnt(&self) -> PcntR {
        PcntR::new(((self.bits >> 19) & 3) as u8)
    }
}
impl W {
    #[doc = "Bits 0:6 - Transfer length"]
    #[inline(always)]
    #[must_use]
    pub fn tlen(&mut self) -> TlenW<Diep0lenSpec> {
        TlenW::new(self, 0)
    }
    #[doc = "Bits 19:20 - Packet count"]
    #[inline(always)]
    #[must_use]
    pub fn pcnt(&mut self) -> PcntW<Diep0lenSpec> {
        PcntW::new(self, 19)
    }
}
#[doc = "device IN endpoint-0 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep0len::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep0len::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Diep0lenSpec;
impl crate::RegisterSpec for Diep0lenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diep0len::R`](R) reader structure"]
impl crate::Readable for Diep0lenSpec {}
#[doc = "`write(|w| ..)` method takes [`diep0len::W`](W) writer structure"]
impl crate::Writable for Diep0lenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DIEP0LEN to value 0"]
impl crate::Resettable for Diep0lenSpec {
    const RESET_VALUE: u32 = 0;
}
