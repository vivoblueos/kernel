#[doc = "Register `DOEP2LEN` reader"]
pub type R = crate::R<Doep2lenSpec>;
#[doc = "Register `DOEP2LEN` writer"]
pub type W = crate::W<Doep2lenSpec>;
#[doc = "Field `TLEN` reader - Transfer length"]
pub type TlenR = crate::FieldReader<u32>;
#[doc = "Field `TLEN` writer - Transfer length"]
pub type TlenW<'a, REG> = crate::FieldWriter<'a, REG, 19, u32>;
#[doc = "Field `PCNT` reader - Packet count"]
pub type PcntR = crate::FieldReader<u16>;
#[doc = "Field `PCNT` writer - Packet count"]
pub type PcntW<'a, REG> = crate::FieldWriter<'a, REG, 10, u16>;
#[doc = "Field `STPCNT_RXDPID` reader - SETUP packet count/Received data PID"]
pub type StpcntRxdpidR = crate::FieldReader;
#[doc = "Field `STPCNT_RXDPID` writer - SETUP packet count/Received data PID"]
pub type StpcntRxdpidW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:18 - Transfer length"]
    #[inline(always)]
    pub fn tlen(&self) -> TlenR {
        TlenR::new(self.bits & 0x0007_ffff)
    }
    #[doc = "Bits 19:28 - Packet count"]
    #[inline(always)]
    pub fn pcnt(&self) -> PcntR {
        PcntR::new(((self.bits >> 19) & 0x03ff) as u16)
    }
    #[doc = "Bits 29:30 - SETUP packet count/Received data PID"]
    #[inline(always)]
    pub fn stpcnt_rxdpid(&self) -> StpcntRxdpidR {
        StpcntRxdpidR::new(((self.bits >> 29) & 3) as u8)
    }
}
impl W {
    #[doc = "Bits 0:18 - Transfer length"]
    #[inline(always)]
    #[must_use]
    pub fn tlen(&mut self) -> TlenW<Doep2lenSpec> {
        TlenW::new(self, 0)
    }
    #[doc = "Bits 19:28 - Packet count"]
    #[inline(always)]
    #[must_use]
    pub fn pcnt(&mut self) -> PcntW<Doep2lenSpec> {
        PcntW::new(self, 19)
    }
    #[doc = "Bits 29:30 - SETUP packet count/Received data PID"]
    #[inline(always)]
    #[must_use]
    pub fn stpcnt_rxdpid(&mut self) -> StpcntRxdpidW<Doep2lenSpec> {
        StpcntRxdpidW::new(self, 29)
    }
}
#[doc = "device OUT endpoint-2 transfer length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep2len::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep2len::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Doep2lenSpec;
impl crate::RegisterSpec for Doep2lenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`doep2len::R`](R) reader structure"]
impl crate::Readable for Doep2lenSpec {}
#[doc = "`write(|w| ..)` method takes [`doep2len::W`](W) writer structure"]
impl crate::Writable for Doep2lenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DOEP2LEN to value 0"]
impl crate::Resettable for Doep2lenSpec {
    const RESET_VALUE: u32 = 0;
}
