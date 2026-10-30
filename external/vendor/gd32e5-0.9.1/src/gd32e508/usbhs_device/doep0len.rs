#[doc = "Register `DOEP0LEN` reader"]
pub type R = crate::R<Doep0lenSpec>;
#[doc = "Register `DOEP0LEN` writer"]
pub type W = crate::W<Doep0lenSpec>;
#[doc = "Field `TLEN` reader - Transfer length"]
pub type TlenR = crate::FieldReader;
#[doc = "Field `TLEN` writer - Transfer length"]
pub type TlenW<'a, REG> = crate::FieldWriter<'a, REG, 7>;
#[doc = "Field `PCNT` reader - Packet count"]
pub type PcntR = crate::BitReader;
#[doc = "Field `PCNT` writer - Packet count"]
pub type PcntW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STPCNT` reader - SETUP packet count"]
pub type StpcntR = crate::FieldReader;
#[doc = "Field `STPCNT` writer - SETUP packet count"]
pub type StpcntW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:6 - Transfer length"]
    #[inline(always)]
    pub fn tlen(&self) -> TlenR {
        TlenR::new((self.bits & 0x7f) as u8)
    }
    #[doc = "Bit 19 - Packet count"]
    #[inline(always)]
    pub fn pcnt(&self) -> PcntR {
        PcntR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bits 29:30 - SETUP packet count"]
    #[inline(always)]
    pub fn stpcnt(&self) -> StpcntR {
        StpcntR::new(((self.bits >> 29) & 3) as u8)
    }
}
impl W {
    #[doc = "Bits 0:6 - Transfer length"]
    #[inline(always)]
    #[must_use]
    pub fn tlen(&mut self) -> TlenW<Doep0lenSpec> {
        TlenW::new(self, 0)
    }
    #[doc = "Bit 19 - Packet count"]
    #[inline(always)]
    #[must_use]
    pub fn pcnt(&mut self) -> PcntW<Doep0lenSpec> {
        PcntW::new(self, 19)
    }
    #[doc = "Bits 29:30 - SETUP packet count"]
    #[inline(always)]
    #[must_use]
    pub fn stpcnt(&mut self) -> StpcntW<Doep0lenSpec> {
        StpcntW::new(self, 29)
    }
}
#[doc = "device OUT endpoint-0 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep0len::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep0len::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Doep0lenSpec;
impl crate::RegisterSpec for Doep0lenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`doep0len::R`](R) reader structure"]
impl crate::Readable for Doep0lenSpec {}
#[doc = "`write(|w| ..)` method takes [`doep0len::W`](W) writer structure"]
impl crate::Writable for Doep0lenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DOEP0LEN to value 0"]
impl crate::Resettable for Doep0lenSpec {
    const RESET_VALUE: u32 = 0;
}
