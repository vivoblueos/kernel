#[doc = "Register `DOEP5INTF` reader"]
pub type R = crate::R<Doep5intfSpec>;
#[doc = "Register `DOEP5INTF` writer"]
pub type W = crate::W<Doep5intfSpec>;
#[doc = "Field `TF` reader - Transfer finished"]
pub type TfR = crate::BitReader;
#[doc = "Field `TF` writer - Transfer finished"]
pub type TfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EPDIS` reader - Endpoint disabled"]
pub type EpdisR = crate::BitReader;
#[doc = "Field `EPDIS` writer - Endpoint disabled"]
pub type EpdisW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STPF` reader - Setup phase finished"]
pub type StpfR = crate::BitReader;
#[doc = "Field `STPF` writer - Setup phase finished"]
pub type StpfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EPRXFOVR` reader - Endpoint Rx FIFO overrun"]
pub type EprxfovrR = crate::BitReader;
#[doc = "Field `EPRXFOVR` writer - Endpoint Rx FIFO overrun"]
pub type EprxfovrW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BTBSTP` reader - Back-to-back SETUP packets"]
pub type BtbstpR = crate::BitReader;
#[doc = "Field `BTBSTP` writer - Back-to-back SETUP packets"]
pub type BtbstpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NYET` reader - NYET handshake is sent"]
pub type NyetR = crate::BitReader;
#[doc = "Field `NYET` writer - NYET handshake is sent"]
pub type NyetW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Transfer finished"]
    #[inline(always)]
    pub fn tf(&self) -> TfR {
        TfR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Endpoint disabled"]
    #[inline(always)]
    pub fn epdis(&self) -> EpdisR {
        EpdisR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 3 - Setup phase finished"]
    #[inline(always)]
    pub fn stpf(&self) -> StpfR {
        StpfR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Endpoint Rx FIFO overrun"]
    #[inline(always)]
    pub fn eprxfovr(&self) -> EprxfovrR {
        EprxfovrR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 6 - Back-to-back SETUP packets"]
    #[inline(always)]
    pub fn btbstp(&self) -> BtbstpR {
        BtbstpR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 14 - NYET handshake is sent"]
    #[inline(always)]
    pub fn nyet(&self) -> NyetR {
        NyetR::new(((self.bits >> 14) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Transfer finished"]
    #[inline(always)]
    #[must_use]
    pub fn tf(&mut self) -> TfW<Doep5intfSpec> {
        TfW::new(self, 0)
    }
    #[doc = "Bit 1 - Endpoint disabled"]
    #[inline(always)]
    #[must_use]
    pub fn epdis(&mut self) -> EpdisW<Doep5intfSpec> {
        EpdisW::new(self, 1)
    }
    #[doc = "Bit 3 - Setup phase finished"]
    #[inline(always)]
    #[must_use]
    pub fn stpf(&mut self) -> StpfW<Doep5intfSpec> {
        StpfW::new(self, 3)
    }
    #[doc = "Bit 4 - Endpoint Rx FIFO overrun"]
    #[inline(always)]
    #[must_use]
    pub fn eprxfovr(&mut self) -> EprxfovrW<Doep5intfSpec> {
        EprxfovrW::new(self, 4)
    }
    #[doc = "Bit 6 - Back-to-back SETUP packets"]
    #[inline(always)]
    #[must_use]
    pub fn btbstp(&mut self) -> BtbstpW<Doep5intfSpec> {
        BtbstpW::new(self, 6)
    }
    #[doc = "Bit 14 - NYET handshake is sent"]
    #[inline(always)]
    #[must_use]
    pub fn nyet(&mut self) -> NyetW<Doep5intfSpec> {
        NyetW::new(self, 14)
    }
}
#[doc = "device out endpoint-5 interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep5intf::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep5intf::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Doep5intfSpec;
impl crate::RegisterSpec for Doep5intfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`doep5intf::R`](R) reader structure"]
impl crate::Readable for Doep5intfSpec {}
#[doc = "`write(|w| ..)` method takes [`doep5intf::W`](W) writer structure"]
impl crate::Writable for Doep5intfSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DOEP5INTF to value 0"]
impl crate::Resettable for Doep5intfSpec {
    const RESET_VALUE: u32 = 0;
}
