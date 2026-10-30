#[doc = "Register `CTL3` reader"]
pub type R = crate::R<Ctl3Spec>;
#[doc = "Register `CTL3` writer"]
pub type W = crate::W<Ctl3Spec>;
#[doc = "Field `RTEN` reader - Receiver timeout enable"]
pub type RtenR = crate::BitReader;
#[doc = "Field `RTEN` writer - Receiver timeout enable"]
pub type RtenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SCRTNUM` reader - Smartcard auto-retry number"]
pub type ScrtnumR = crate::FieldReader;
#[doc = "Field `SCRTNUM` writer - Smartcard auto-retry number"]
pub type ScrtnumW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `RTIE` reader - Interrupt enable bit of receive timeout event"]
pub type RtieR = crate::BitReader;
#[doc = "Field `RTIE` writer - Interrupt enable bit of receive timeout event"]
pub type RtieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EBIE` reader - Interrupt enable bit of end of block event"]
pub type EbieR = crate::BitReader;
#[doc = "Field `EBIE` writer - Interrupt enable bit of end of block event"]
pub type EbieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RINV` reader - RX pin level inversion"]
pub type RinvR = crate::BitReader;
#[doc = "Field `RINV` writer - RX pin level inversion"]
pub type RinvW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TINV` reader - TX pin level inversion"]
pub type TinvR = crate::BitReader;
#[doc = "Field `TINV` writer - TX pin level inversion"]
pub type TinvW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DINV` reader - Data bit level inversion"]
pub type DinvR = crate::BitReader;
#[doc = "Field `DINV` writer - Data bit level inversion"]
pub type DinvW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MSBF` reader - Most significant bit first"]
pub type MsbfR = crate::BitReader;
#[doc = "Field `MSBF` writer - Most significant bit first"]
pub type MsbfW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Receiver timeout enable"]
    #[inline(always)]
    pub fn rten(&self) -> RtenR {
        RtenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:3 - Smartcard auto-retry number"]
    #[inline(always)]
    pub fn scrtnum(&self) -> ScrtnumR {
        ScrtnumR::new(((self.bits >> 1) & 7) as u8)
    }
    #[doc = "Bit 4 - Interrupt enable bit of receive timeout event"]
    #[inline(always)]
    pub fn rtie(&self) -> RtieR {
        RtieR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Interrupt enable bit of end of block event"]
    #[inline(always)]
    pub fn ebie(&self) -> EbieR {
        EbieR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 8 - RX pin level inversion"]
    #[inline(always)]
    pub fn rinv(&self) -> RinvR {
        RinvR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - TX pin level inversion"]
    #[inline(always)]
    pub fn tinv(&self) -> TinvR {
        TinvR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Data bit level inversion"]
    #[inline(always)]
    pub fn dinv(&self) -> DinvR {
        DinvR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Most significant bit first"]
    #[inline(always)]
    pub fn msbf(&self) -> MsbfR {
        MsbfR::new(((self.bits >> 11) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Receiver timeout enable"]
    #[inline(always)]
    #[must_use]
    pub fn rten(&mut self) -> RtenW<Ctl3Spec> {
        RtenW::new(self, 0)
    }
    #[doc = "Bits 1:3 - Smartcard auto-retry number"]
    #[inline(always)]
    #[must_use]
    pub fn scrtnum(&mut self) -> ScrtnumW<Ctl3Spec> {
        ScrtnumW::new(self, 1)
    }
    #[doc = "Bit 4 - Interrupt enable bit of receive timeout event"]
    #[inline(always)]
    #[must_use]
    pub fn rtie(&mut self) -> RtieW<Ctl3Spec> {
        RtieW::new(self, 4)
    }
    #[doc = "Bit 5 - Interrupt enable bit of end of block event"]
    #[inline(always)]
    #[must_use]
    pub fn ebie(&mut self) -> EbieW<Ctl3Spec> {
        EbieW::new(self, 5)
    }
    #[doc = "Bit 8 - RX pin level inversion"]
    #[inline(always)]
    #[must_use]
    pub fn rinv(&mut self) -> RinvW<Ctl3Spec> {
        RinvW::new(self, 8)
    }
    #[doc = "Bit 9 - TX pin level inversion"]
    #[inline(always)]
    #[must_use]
    pub fn tinv(&mut self) -> TinvW<Ctl3Spec> {
        TinvW::new(self, 9)
    }
    #[doc = "Bit 10 - Data bit level inversion"]
    #[inline(always)]
    #[must_use]
    pub fn dinv(&mut self) -> DinvW<Ctl3Spec> {
        DinvW::new(self, 10)
    }
    #[doc = "Bit 11 - Most significant bit first"]
    #[inline(always)]
    #[must_use]
    pub fn msbf(&mut self) -> MsbfW<Ctl3Spec> {
        MsbfW::new(self, 11)
    }
}
#[doc = "Control register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl3::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl3::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl3Spec;
impl crate::RegisterSpec for Ctl3Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl3::R`](R) reader structure"]
impl crate::Readable for Ctl3Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl3::W`](W) writer structure"]
impl crate::Writable for Ctl3Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL3 to value 0"]
impl crate::Resettable for Ctl3Spec {
    const RESET_VALUE: u32 = 0;
}
